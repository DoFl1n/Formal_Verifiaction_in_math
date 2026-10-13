/-!
# Seminar 3
Quantifiers, tactics
-/

/- Universal Quantifier -/
variable (α : Type) (P Q : α → Prop)

#check ∀ (x : α), P x
#check ∀ x : α, P x
#check ∀ x, P x
#check ∀ x y : α, P x ∧ Q y
#check ∀ x : α, ∀ y : α, P x ∧ Q y
#check (x : α) → P x

example : (∀ x : α, P x) ∨ (∀ x : α, Q x) → ∀ x : α, P x ∨ Q x  :=
  λ h x ↦ Or.elim h (λ hP ↦ Or.inl (hP x)) (λ hQ ↦ Or.inr (hQ x))

example : (∀ (x : α), P x ∧ Q x) ↔ (∀ x : α, P x) ∧ (∀ x : α, Q x) :=
  sorry

/- Existential Quantifier -/

#check ∃ (x : α), P x
#check Exists P
#print Exists -- ?
#check Exists.intro

/- Why not this?
structure Exists' {α : Type} {P : α → Prop} : Prop where
  intro ::
  a : α
  b : P a
-/

example : (∃ x : α, P x ∧ Q x) → (∃ x : α, P x) ∧ (∃ x : α, Q x) :=
  λ ⟨x, hp, hq⟩ ↦ ⟨⟨x, hp⟩, ⟨x, hq⟩⟩

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  sorry


/- Cantor theorem -/

/- 2^α ≃ α → Prop (at least classicaly) -/
theorem cantor (f : α → (α → Prop)) :
 ¬∀ S : α → Prop, ∃ x : α, ∀ y : α, S y ↔ f x y :=
  sorry

/- Classical logic -/

theorem not_exists_not : (¬ ∃ x : α, ¬ P x) → ∀ x : α, P x :=
  λ h x ↦ Or.elim (Classical.em (P x)) id (λ hn ↦ False.elim (h ⟨x, hn⟩))

theorem forall_or_exists_not : (∀ x : α, P x) ∨ (∃ x : α, ¬ P x) :=
  sorry

example (people : Type) (Joe : people) (drinks : people → Prop) :
  ∃ x : people, drinks x → ∀ y : people, drinks y :=
  sorry

/- Tactics -/

variable (p q r : Prop)

/- Intro, exact, apply, assumption -/

theorem ex1 : p → p := by
  intro hp
  exact hp

#print ex1

theorem ex2 : p → q → p := by
  intro hp
  intro hq
  exact hp

#print ex2

theorem ex3 : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  exact (hqr (hpq hp))

#print ex3

theorem ex3' : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

#print ex3'

theorem ex4 : (p → (q → r)) → (p → q) → p → r := by
  intro hpqr hpq hp
  apply hpqr
  · exact hp
  · apply hpq
    apply hp

#print ex4

theorem ex5 : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  apply Or.elim hqr
  . intro hq
    apply Or.inl
    apply And.intro
    . assumption
    . assumption
  . intro hr
    apply Or.inr
    apply And.intro
    . assumption
    . assumption

#print ex5

example : (p → q) → (¬ q → ¬ p) := by
  sorry

example : p ∧ q ↔ q ∧ p := by
  sorry

/- cases, constructor, left/right, exists -/

example : p ∨ q → q ∨ p := by
  intro hpq
  cases hpq
  case inl hp =>
    right
    assumption
  case inr =>
    left
    assumption

example : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := by
  intro h
  cases h
  case inl hpq =>
    constructor
    · exact hpq.1
    · left
      apply hpq.2
  case inr hpr =>
    have ⟨hp, hr⟩ := hpr
    constructor
    · assumption
    · right
      assumption

example : p ∨ q → ¬ (¬ p ∧ ¬ q) := by
  sorry

example : (∀ x : α, P x) ∨ (∀ x : α, Q x) → ∀ x : α, P x ∨ Q x  := by
  intro h x
  cases h
  case inl h =>
    left
    apply h
  case inr h =>
    right
    apply h

example : (∃ x : α, P x ∧ Q x) → (∃ x : α, P x) ∧ (∃ x : α, Q x) := by
  intro ⟨x, hP, hQ⟩
  constructor
  · exists x
  · exists x

example : (∀ (x : α), P x ∧ Q x) ↔ (∀ x : α, P x) ∧ (∀ x : α, Q x) :=
  sorry

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  sorry

/- Tactic combinators -/

example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl; assumption

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

example (p q r : Prop) (hp : p) :
  (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  sorry

/- Make your own tactic -/

-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

macro_rules | `(tactic| triv) => `(tactic| constructor <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv

/-!
# Exercises
-/
section hw
  example : ∀ p q : Prop, p ∧ q ↔ ∀ r : Prop, (p → q → r) → r :=
    sorry

  example : ∀ p q : Prop, p ∨ q ↔ ∀ r : Prop, (p → r) → (q → r) → r :=
    sorry

  example : (∃ x : α, P x) ↔ ∀ r : Prop, (∀ x : α, P x → r) → r :=
    sorry

  theorem knaster_tarski
    (R : α → α → Prop)
    (trans : ∀ x y z : α, R x y → R y z → R x z)
    (inf : ∀ P : α → Prop, ∃ m : α,
      (∀ x : α, P x → R m x) ∧
      (∀ z : α, (∀ x : α, P x → R z x) → R z m))
    (f : α → α)
    (mono : ∀ x y : α, R x y → R (f x) (f y)) :
    ∃ p : α, R (f p) p ∧ R p (f p) := sorry

  /-- Explain what this theorem means --/
  theorem girard
    (π : (Type → Type) → Type)
    (Λ : ∀ {X : Type → Type}, ((α : Type) → X α) → π X)
    (ε : ∀ {X : Type → Type}, π X → (α : Type) → X α)
    (β : ∀ {X : Type → Type} (f : (α : Type) → X α) (α : Type),
      ∀ (P : X α → Prop), P (ε (Λ f) α) ↔ P (f α))
    : False :=
    sorry
end hw
