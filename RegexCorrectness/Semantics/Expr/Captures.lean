import Regex.Data.Expr
import RegexCorrectness.Semantics.Expr.Matches

import Batteries.Data.String

open String (Pos)

namespace Regex.Data

-- TODO: do we need theory like the mutable heap in Separation Logic?
def Groups : Type := Nat → Option (Pos × Pos)

def Groups.empty : Groups := fun _ => .none

def Groups.insert (g : Groups) (tag : Nat) (first last : Pos) : Groups :=
  fun i => if i = tag then .some (first, last) else g i

def Groups.orElse (g₁ : Groups) (g₂ : Unit → Groups) : Groups :=
  fun tag => g₁ tag <|> g₂ () tag

instance : EmptyCollection Groups := ⟨Groups.empty⟩
instance : OrElse Groups := ⟨Groups.orElse⟩

notation:max g "{" tag "↦" "(" l ", " m ")" "}" =>
  Groups.insert g tag (Pos.mk (String.utf8Len l)) (Pos.mk (String.utf8Len l + String.utf8Len m))

inductive Expr.captures : (l m r : List Char) → (groups : Groups) → (e : Expr) → Prop where
  | char (c : Char) : Expr.captures l [c] r ∅ (.char c)
  | sparse (cs : Classes) (c : Char) (h : c ∈ cs) :
    Expr.captures l [c] r ∅ (.classes cs)
  | epsilon : Expr.captures l [] r ∅ .epsilon
  | group (h : Expr.captures l m r g e) :
    Expr.captures l m r g{tag ↦ (l, m)} (.group tag e)
  | alternateLeft {l m r g e₁ e₂} : Expr.captures l m r g e₁ → Expr.captures l m r g (.alternate e₁ e₂)
  | alternateRight {l m r g e₁ e₂} : Expr.captures l m r g e₂ → Expr.captures l m r g (.alternate e₁ e₂)
  | concat {l m₁ m₂ r g₁ g₂ e₁ e₂} :
    Expr.captures l m₁ (m₂ ++ r) g₁ e₁ → Expr.captures (l ++ m₁) m₂ r g₂ e₂ →
    Expr.captures l (m₁ ++ m₂) r (g₂ <|> g₁) (.concat e₁ e₂)
  | starEpsilon : Expr.captures l [] r ∅ (.star e)
  | starConcat {l m₁ m₂ r g₁ g₂ e} :
    Expr.captures l m₁ (m₂ ++ r) g₁ e → Expr.captures (l ++ m₁) m₂ r g₂ (.star e) →
    Expr.captures l (m₁ ++ m₂) r (g₂ <|> g₁) (.star e)

theorem Expr.matches_iff_captures {e : Expr} {m : List Char} (l r : List Char) :
  e.matches m ↔ ∃ g, e.captures l m r g := by
  apply Iff.intro
  . intro m
    induction m generalizing l r with
    | char c => exact ⟨∅, Expr.captures.char c⟩
    | sparse cs c h => exact ⟨∅, Expr.captures.sparse cs c h⟩
    | epsilon => exact ⟨∅, Expr.captures.epsilon⟩
    | group _ ih =>
      have ⟨g, c⟩ := ih l r
      exact ⟨g{_ ↦ (l, _)}, Expr.captures.group c⟩
    | alternateLeft _ ih =>
      have ⟨g, c⟩ := ih l r
      exact ⟨g, Expr.captures.alternateLeft c⟩
    | alternateRight _ ih =>
      have ⟨g, c⟩ := ih l r
      exact ⟨g, Expr.captures.alternateRight c⟩
    | concat cs₁ cs₂ _ _ _ _ ih₁ ih₂ =>
      have ⟨g₁, c₁⟩ := ih₁ l (cs₂ ++ r)
      have ⟨g₂, c₂⟩ := ih₂ (l ++ cs₁) r
      exact ⟨g₂ <|> g₁, Expr.captures.concat c₁ c₂⟩
    | starEpsilon => exact ⟨Groups.empty, Expr.captures.starEpsilon⟩
    | starConcat cs₁ cs₂ _ _ _ ih₁ ih₂ =>
      have ⟨g₁, c₁⟩ := ih₁ l (cs₂ ++ r)
      have ⟨g₂, c₂⟩ := ih₂ (l ++ cs₁) r
      exact ⟨g₂ <|> g₁, Expr.captures.starConcat c₁ c₂⟩
  . intro ⟨g, c⟩
    induction c with
    | char c => exact Expr.matches.char c
    | sparse cs c h => exact Expr.matches.sparse cs c h
    | epsilon => exact Expr.matches.epsilon
    | group _ ih => exact Expr.matches.group ih
    | alternateLeft _ ih => exact Expr.matches.alternateLeft ih
    | alternateRight _ ih => exact Expr.matches.alternateRight ih
    | concat  _ _ ih₁ ih₂ => exact Expr.matches.concat _ _ _ _ ih₁ ih₂
    | starEpsilon => exact Expr.matches.starEpsilon
    | starConcat _ _ ih₁ ih₂ => exact Expr.matches.starConcat _ _ _ ih₁ ih₂

end Regex.Data
