/-
Copyright (c) 2026 Shedarshian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shedarshian
-/

import Mathlib
/- zfc -/
namespace zfset

section belong_set

axiom set : Type
axiom belong_set (x : set) (y : set) : Prop
def not_belong_set (x : set) (y : set) : Prop := ¬belong_set x y
local infix:50 " ∈ " => belong_set
local infix:50 " ∉ " => not_belong_set

axiom axiom_of_extensionality {x y} : (∀ a, a ∈ x ↔ a ∈ y) → x = y

theorem extensionality_iff {x y} : (∀ a, a ∈ x ↔ a ∈ y) ↔ x = y :=
by
  apply Iff.intro;
  · exact axiom_of_extensionality;
  intro h;
  rw [h];
  simp;

def Class : Type := set → Prop

def set.to_Class (a : set) : Class := fun x : set => x ∈ a
noncomputable instance set_to_class_coe : Coe set Class := ⟨ set.to_Class ⟩
def Class.is_set (A : Class) : Prop := ∃ x : set, x.to_Class = A
def Class.is_proper (A : Class) : Prop := ¬A.is_set

class has_belong (α : Type u) where
(belong : α → set → Prop)
(extensionality {x y : α} : (∀ a, belong x a ↔ belong y a) ↔ x = y)
(to_Class : α → Class)
(proof_Class {x : α} : ∀ a : set, belong x a ↔ to_Class x a)
(is_set : α → Prop)
class has_belonged_to (α : Type u) where
(belonged_to {β : Type v} [has_belong β] : α → β → Prop)

noncomputable instance set.to_has_belong : has_belong set :=
⟨ fun x y => belong_set y x, @extensionality_iff, set.to_Class, by {intros; rfl}, fun s => True ⟩
instance Class.to_has_belong : has_belong Class :=
⟨ id, by {
  intros;
  apply Iff.intro <;> intro h
  · unfold id at h;
    apply funext;
    intro a;
    exact propext (h a);
  · intros; rw [h]
}, id, by {intros; rfl}, Class.is_set ⟩
def set.belonged_to {β : Type _} [s : has_belong β] (a : set) (b : β) : Prop :=
  has_belong.belong b a
noncomputable instance set.to_has_belonged_to : has_belonged_to set :=
  ⟨ @set.belonged_to ⟩
def Class.belonged_to {β : Type _} [s : has_belong β] (A : Class) (b : β) : Prop :=
  ∃ a, has_belong.belong b a ∧ ∀ z, z ∈ a ↔ A z
instance Class.to_has_belonged_to : has_belonged_to Class :=
  ⟨ @Class.belonged_to ⟩

end belong_set

def belong {α : Type u} {β : Type v} [r : has_belonged_to α] [s : has_belong β]
(a : α) (b : β) : Prop :=
  has_belonged_to.belonged_to a b

infix:50 " ∈ " => belong
infix:50 " ∉ " => fun x y => ¬belong x y
syntax "∀ " ident " s∈ " term ", " term : term
syntax "∀ " "_" " s∈ " term ", " term : term
macro_rules
| `(∀ $x:ident s∈ $A, $P) =>
    `(∀ $x:ident : set, $x ∈ $A → $P)
| `(∀ _ s∈ $A, $P) =>
    `(∀ x : set, x ∈ $A → $P)
syntax "∃ " ident " s∈ " term ", " term : term
syntax "∃ " "_" " s∈ " term ", " term : term
macro_rules
| `(∃ $x:ident s∈ $A, $P) =>
    `(∃ $x:ident : set, $x ∈ $A ∧ $P)
| `(∃ _ s∈ $A, $P) =>
    `(∃ x : set, x ∈ $A ∧ $P)

theorem proof_to_Class {α : Type u} [has_belong α] {a : α} {b : set} :
b ∈ (has_belong.to_Class a) ↔ b ∈ a :=
by
  unfold belong; unfold_projs; unfold set.belonged_to; unfold_projs;
  unfold id; erw [has_belong.proof_Class];

theorem proof_in_Class {a : set} {B : Class} : a ∈ B ↔ B a :=
by
  unfold belong; unfold_projs; unfold set.belonged_to; unfold_projs;
  unfold id; rfl;

theorem extensionality_belong {α : Type u} [s : has_belong α] {x y : α} :
(∀ a : set, a ∈ x ↔ a ∈ y) ↔ x = y :=
by {exact has_belong.extensionality}

private theorem ex_iff_nonempty {α : Type*} {p : α → Prop} :
(Nonempty {x // p x}) ↔ ∃ x : α, p x :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) (fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩)

noncomputable def Class_to_set (A : Class) (h : A.is_set) :
{x : set // x.to_Class = A} :=
  (Classical.choice (ex_iff_nonempty.2 h))

noncomputable def Class.to_set (A : Class) (h : A.is_set) : set :=
  (Class_to_set A h).1

theorem Class_to_set_ext {A : Class} (h : A.is_set) :
∀ x : set, x ∈ A.to_set h ↔ x ∈ A :=
by
  intro x; unfold Class.to_set;
  have hy := (Class_to_set A h).prop;
  erw [←extensionality_belong] at hy;
  exact hy x;

theorem Class_to_set_to_Class {A : Class} (h : A.is_set) : (A.to_set h).to_Class = A :=
by
  rw [←extensionality_belong]; exact Class_to_set_ext h;

theorem Class_to_set_to_Class_has_belong {A : Class} (h : A.is_set) :
  has_belong.to_Class (A.to_set h) = A :=
by
  rw [←extensionality_belong]; exact Class_to_set_ext h;

theorem set_to_Class_is_set {x : set} : x.to_Class.is_set :=
⟨x, rfl⟩
theorem set_to_Class_to_set {x : set} (h) :
  x.to_Class.to_set h = x := by
  rw [←extensionality_belong]; exact Class_to_set_ext _;
theorem set_to_Class_to_set_has_belong {x : set} (h) :
  (has_belong.to_Class x).to_set h = x := by
  rw [←extensionality_belong]; exact Class_to_set_ext _;

theorem class_belong_is_set {α : Type u} [s : has_belong α] {A : Class} {b : α} :
A ∈ b → A.is_set :=
by
  intro ⟨x, ⟨f, h⟩⟩;
  use x;
  rw [←extensionality_belong]; intro a;
  exact h a;

theorem set_to_class_belong {α : Type u} [s : has_belong α] {a : set} {b : α} :
a.to_Class ∈ b ↔ a ∈ b :=
by
  apply Iff.intro <;> intro h;
  · rcases h with ⟨x, ⟨f, h⟩⟩;
    have h := axiom_of_extensionality h;
    rw [h] at f; exact f;
  use a; use h; intro x;
  unfold set.to_Class; rfl

theorem set_belong_to_class [s : has_belong α]
{a : set} {b : α} :
a ∈ b ↔ a ∈ has_belong.to_Class b := s.4 a
theorem set_belong_set_to_class {a : set} {b : set} :
a ∈ b ↔ a ∈ set.to_Class b := set.to_has_belong.4 a
@[simp] theorem set_belong_to_class2 [s : has_belong α]
  {a : set} {b : α} : a ∈ has_belong.to_Class b ↔ a ∈ b :=
  Iff.comm.1 set_belong_to_class
theorem set_belong_set_to_class2 {a : set} {b : set} :
  a ∈ set.to_Class b ↔ a ∈ b := Iff.comm.1 set_belong_set_to_class

theorem set_eq_iff_class (a b : set) : a = b ↔ a.to_Class = b.to_Class :=
by
  apply Iff.intro <;> intro h;
  · rw [h];
  rw [←extensionality_belong]; intro x;
  have f : a.to_Class x ↔ b.to_Class x;
  · rw [h];
  exact f;

def Russel_class : Class := fun x => x ∉ x
theorem Russel_proper_class : Class.is_proper Russel_class :=
by
  intro ⟨x, f⟩;
  have g := em (x.to_Class x);
  cases g with
  | inl g =>
    have r := g;
    rw [f] at g;
    unfold Russel_class at g;
    exact g r
  | inr g =>
    have r := g;
    rw [f] at g;
    unfold Russel_class at g;
    exact g r

axiom make_pair (a : set) (b : set) : set
@[simp] axiom axiom_of_pair {a b} : ∀ x, x ∈ make_pair a b ↔ x = a ∨ x = b

notation "s{" a ", " b "}" => make_pair a b

@[simp] theorem pair_comm {a b} : s{a, b} = s{b, a} :=
by
  apply axiom_of_extensionality;
  intro x;
  let hab := @axiom_of_pair a b x;
  let hba := @axiom_of_pair b a x;
  rw [Or.comm, ←hba] at hab;
  exact hab;

instance pair_is_commutative : Std.Commutative make_pair :=
⟨ @pair_comm ⟩

@[simp] theorem first_in_pair {a b} : a ∈ s{a, b} :=
by {rw [axiom_of_pair a]; simp}
@[simp] theorem second_in_pair {a b} : b ∈ s{a, b} :=
by {rw [pair_comm]; apply first_in_pair}

noncomputable def one_element_set (a : set) := make_pair a a
notation "s{" a "}" => one_element_set a

@[simp] lemma element_in_one_element_set {a x} : x ∈ s{a} ↔ x = a :=
by {unfold one_element_set; rw [axiom_of_pair]; simp}
lemma one_element_set_eq_iff {a b} : s{a} = s{b} ↔ a = b :=
by
  rw [←extensionality_iff];
  apply Iff.intro <;> intro h;
  · let h2 : ∀ x, x = a ↔ x = b;
    · intro x;
      rw [← element_in_one_element_set];
      rw [← element_in_one_element_set];
      exact h x;
    rw [← h2 a];
  intro x;
  rw [h];

lemma one_element_set_eq_pair_iff {a b c} :
s{a} = s{b, c} ↔ a = b ∧ a = c :=
by
  rw [←extensionality_iff];
  apply Iff.intro <;> intro h;
  · let h2 : ∀ x, x = a ↔ x = b ∨ x = c;
    · intro x;
      rw [←element_in_one_element_set];
      rw [←axiom_of_pair];
      exact h x;
    constructor;
    · let f := h2 b;
      rw [eq_comm] at f;
      rw [f];
      simp;
    let f := h2 c;
    rw [eq_comm] at f;
    rw [f];
    simp;
  rw [←h.1, ←h.2];
  intro x; rfl;

noncomputable def make_ordered_pair (a : set) (b : set) : set :=
s{s{a}, s{a, b}}
notation "s⟨" a ", " b "⟩" => make_ordered_pair a b

@[simp] lemma ordered_pair_eq_iff {a b c d} : s⟨a, b⟩ = s⟨c, d⟩ ↔ a = c ∧ b = d :=
by
  apply Iff.intro <;> intro h;
    swap;
    · rw [h.1, h.2];
  rw [←extensionality_iff] at h;
  have h4 : ∀ x, x = s{a} ∨ x = s{a, b} ↔ x = s{c} ∨ x = s{c, d};
  · intro x;
    have h3 := h x;
    rw [←axiom_of_pair];rw [←axiom_of_pair]; exact h3;
  have h5 := (h4 s{a}).1 (Or.inl (Eq.refl s{a}));
  let hac : a = c;
    cases h5 with
    | inl h5 =>
      rw [one_element_set_eq_iff] at h5;
      exact h5;
    | inr h5 =>
      rw [one_element_set_eq_pair_iff] at h5;
      exact h5.1;
  constructor;
  · exact hac;
  rw [←hac] at h4;
  have h6 := (h4 s{a, b}).1 (Or.inr (Eq.refl s{a, b}));
  cases (em (a = b)) with
  | inl h6 =>
    rw [←h6] at h4;
    have h7 := (h4 s{a, d}).2 (Or.inr (Eq.refl s{a, d}));
    have h7a : s{a, d} = s{a};
      cases h7 with
      | inl h7 => exact h7;
      | inr h7 => exact h7;
    have h7 := Eq.symm h7a;
    rw [one_element_set_eq_pair_iff] at h7;
    rw [←h6]; exact h7.2;
  | inr h1 =>
    cases h6 with
    | inl h6 =>
      have h6 := Eq.symm h6;
      rw [one_element_set_eq_pair_iff] at h6;
      exfalso; exact h1 h6.2;
    | inr h6 =>
      have h7 : ∀ x : set, x ∈ s{a, b} ↔ x ∈ s{a, d};
      · intro x; rw [h6];
      have h8 := @second_in_pair a b;
      rw [h7 b, axiom_of_pair] at h8;
      cases h8 with
      | inl h8 =>
        exfalso; exact h1 (Eq.symm h8);
      | inr h8 => exact h8;

axiom make_union (x : set) : set
axiom axiom_of_union {a} :
∀ x : set, x ∈ make_union a ↔ (∃ y : set, x ∈ y ∧ y ∈ a)

def make_union_class (A : Class) : Class :=
fun x => ∃ y : set, x ∈ y ∧ y ∈ A

class has_union (α : Type u) [has_belong α] where
(union : α → α)
(proof_union {a : α} {b : set} : b ∈ union a ↔ ∃ c : set, b ∈ c ∧ c ∈ a )

noncomputable instance set.to_has_union : has_union set :=
⟨ make_union, @axiom_of_union ⟩
instance Class.to_make_union : has_union Class :=
⟨ make_union_class, by {intros; rfl} ⟩
def make_union_reloaded
  {α : Type u} [has_belong α] [has_union α] (a : α)
  : α :=
has_union.union a

notation "∪(" a ")" => make_union_reloaded a

noncomputable def union_set (a b : set) : set :=
∪(s{a, b})
def union_class (A B : Class) : Class :=
fun x => x ∈ A ∨ x ∈ B
def intersection_class (A B : Class) : Class :=
fun x => x ∈ A ∧ x ∈ B

theorem union_set_is_union {a b : set} :
∀ x : set, x ∈ union_set a b ↔ x ∈ a ∨ x ∈ b :=
by
  intro x;
  erw [axiom_of_union];
  apply Iff.intro <;> intro h3;
  · rcases h3 with ⟨y, h3⟩;
    rw [axiom_of_pair] at h3;
    rw [and_or_left] at h3;
    cases h3 with
    | inl h3 =>
      left; rw [← h3.2]; exact h3.1;
    | inr h3 =>
      right; rw [← h3.2]; exact h3.1;
  cases h3 with
  | inl h3 =>
    existsi a; exact ⟨h3, first_in_pair⟩;
  | inr h3 =>
    existsi b; exact ⟨h3, second_in_pair⟩;

class has_binary_union (α : Type u) [has_belong α] where
(binary_union : α → α → α)
(proof_union {a b : α} {c : set} : c ∈ binary_union a b ↔ c ∈ a ∨ c ∈ b)

noncomputable instance set.to_has_binary_union
  : has_binary_union set :=
⟨ union_set, @union_set_is_union ⟩
instance Class.to_has_binary_union
  : has_binary_union Class :=
⟨ union_class, by {intros; rfl} ⟩

def binary_union
  {α : Type u} [has_belong α] [has_binary_union α] (a b : α)
  : α :=
has_binary_union.binary_union a b

infixl:65 " ∪ " => binary_union

@[simp] theorem binary_union_comm
  {α : Type u} [has_belong α] [has_binary_union α] {a b : α} :
a ∪ b = b ∪ a :=
by
  rw [← extensionality_belong];
  intro x;
  repeat erw [has_binary_union.proof_union];
  exact or_comm;

instance binary_union_is_commutative
  {α : Type u} [s1 : has_belong α] [s2 : has_binary_union α]
  : @Std.Commutative α binary_union :=
⟨ @binary_union_comm α s1 s2⟩

@[simp] theorem binary_union_assoc
  {α : Type u} [has_belong α] [has_binary_union α] {a b c : α} :
(a ∪ b) ∪ c = a ∪ (b ∪ c) :=
by
  rw [← extensionality_belong];
  intro x;
  repeat erw [has_binary_union.proof_union];
  exact or_assoc;

instance binary_union_is_associative
  (α : Type u) [s1 : has_belong α] [s2 : has_binary_union α]
  : @Std.Associative α binary_union :=
⟨ @binary_union_assoc α s1 s2 ⟩

@[simp] theorem binary_union_def [has_belong α] [has_binary_union α]
{a b : α} (x : set) :
x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
by erw [has_binary_union.proof_union];

theorem set_binary_union_class (a b : set) :
a.to_Class ∪ b.to_Class = (a ∪ b).to_Class := by
  rw [←extensionality_belong]; intro x; simp only [binary_union_def];
  rw [←set_belong_set_to_class, ←set_belong_set_to_class,
    ←set_belong_set_to_class]; simp;

class has_intersection (α : Type u) (β : Type v)
  [s : has_belong α] [t : has_belong β] where
(intersection : α → β → α)
(proof_intersection {a : α} {b : β} {c : set} : c ∈ intersection a b ↔ c ∈ a ∧ c ∈ b)

instance Class.to_has_intersection
  : has_intersection Class Class :=
⟨ intersection_class, by {intros; rfl} ⟩

instance : has_intersection Class set :=
⟨ fun A B x => x ∈ A ∧ x ∈ B, by {intros; rfl} ⟩

def intersection
  {α : Type u} {β : Type v} [s : has_belong α] [t : has_belong β]
  [t2 : has_intersection α β] (a : α) (b : β)
  : α :=
has_intersection.intersection a b

infixl:70 " ∩ " => intersection

@[simp] theorem intersection_comm [has_belong α] [has_intersection α α]
  {a b : α} :
a ∩ b = b ∩ a :=
by
  erw [← extensionality_belong];
  intro x;
  repeat erw [has_intersection.proof_intersection];
  exact and_comm;

instance intersection_is_commutative
  (α : Type u) [t : has_belong α] [s : has_intersection α α]
  : @Std.Commutative α intersection :=
⟨ @intersection_comm α t s ⟩

@[simp] theorem intersection_assoc [has_belong α] [has_belong β] [has_belong γ]
  [has_intersection α β] [has_intersection β γ] [has_intersection α γ]
  {a : α} {b : β} {c : γ} :
  (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
by
  erw [← extensionality_belong];
  intro x;
  repeat erw [has_intersection.proof_intersection];
  exact and_assoc;

instance intersection_is_associative
  (α : Type u) [t : has_belong α] [s : has_intersection α α]
  : @Std.Associative α intersection :=
⟨ @intersection_assoc α α α t t t s s s ⟩

@[simp] theorem intersection_def [has_belong α]
[has_belong β] [has_intersection α β]
{a : α} {b : β} (x : set) :
x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
by erw [has_intersection.proof_intersection];

theorem intersection_to_class {A : Class} {b : set} : A ∩ b = A ∩ b.to_Class := by
  rw [←extensionality_belong]; intro a;
  simp only [intersection_def, and_congr_right_iff];
  rw [set_belong_set_to_class]; simp only [implies_true];

theorem intersection_to_class_has_belong [has_belong α] [has_intersection Class α]
  {A : Class} {b : α} :
  A ∩ b = A ∩ has_belong.to_Class b := by
  rw [←extensionality_belong]; intro a;
  simp only [intersection_def, and_congr_right_iff];
  rw [←set_belong_to_class]; simp only [implies_true];

axiom empty_set : set
axiom axiom_of_empty {x : set} : x ∉ empty_set
notation "s0" => empty_set
theorem empty_false {x : set} : x ∈ s0 ↔ False :=
by {
  apply Iff.intro;
  · exact axiom_of_empty;
  intro h; exfalso; exact h;
}

theorem nonempty_iff_has_element {a : set} :
a ≠ s0 ↔ ∃ x : set, x ∈ a :=
by
  apply Iff.intro <;> intro h;
  swap;
  · intro f;
    rw [f] at h;
    rcases h with ⟨x, h⟩;
    exact axiom_of_empty h;
  have h : ¬a = s0 := h;
  rw [← extensionality_belong] at h;
  push Not at h;
  rcases h with ⟨x, h⟩;
  use x;
  rw [empty_false] at h;
  cases h with
  | inl h => exact h.1;
  | inr h => exfalso; exact h.2;

theorem nonempty_class_iff_has_element {a : Class} :
a ≠ s0 ↔ ∃ x : set, x ∈ a :=
by
  apply Iff.intro <;> intro h;
    swap;
  · intro f;
    rw [f] at h;
    rcases h with ⟨x, h⟩;
    exact axiom_of_empty h;
  have h : ¬a = s0 := h;
  rw [← extensionality_belong] at h;
  push Not at h;
  rcases h with ⟨x, h⟩;
  use x;
  erw [empty_false] at h;
  cases h with
  | inl h => exact h.1;
  | inr h => exfalso; exact h.2;

@[simp] theorem union_set_empty {a : set} :
a ∪ s0 = a :=
by
  erw [← extensionality_belong];
  intro x;
  erw [has_binary_union.proof_union];
  rw [empty_false];
  rw [or_false];

@[simp] theorem union_class_empty {a : Class} :
a ∪ s0 = a :=
by
  erw [← extensionality_belong];
  intro x;
  erw [has_binary_union.proof_union];
  erw [empty_false];
  rw [or_false];

@[simp] theorem union_empty_set {a : set} : s0 ∪ a = a :=
by rw [binary_union_comm, union_set_empty]
@[simp] theorem union_empty_class {a : Class} : ↑s0 ∪ a = a :=
by rw [binary_union_comm, union_class_empty]

instance empty_is_right_id_union
  : @Std.RightIdentity set set binary_union s0 := ⟨⟩
instance empty_is_right_id_union_class
  : @Std.RightIdentity Class Class binary_union s0 := ⟨⟩
instance empty_is_left_id_union
  : @Std.RightIdentity set set binary_union s0 := ⟨⟩
instance empty_is_left_id_union_class
  : @Std.RightIdentity Class Class binary_union s0 := ⟨⟩

@[simp] theorem intersection_class_empty {a : Class} : a ∩ (set.to_Class s0) = s0 :=
by
  erw [← extensionality_belong];
  intro x;
  erw [has_intersection.proof_intersection];
  erw [empty_false];
  rw [and_false];

@[simp] theorem intersection_empty_class {a : Class} : (set.to_Class s0) ∩ a = s0
:= by rw [intersection_comm, intersection_class_empty]

@[simp] theorem binary_union_self
  {α : Type u} [has_belong α] [has_binary_union α] {a : α} :
a ∪ a = a :=
by
  rw [← extensionality_belong];
  intro x;
  erw [has_binary_union.proof_union];
  rw [or_self];

instance binary_union_is_idempotent
  {α : Type u} [s1 : has_belong α] [s2 : has_binary_union α] :
  @Std.IdempotentOp α binary_union :=
  ⟨ @binary_union_self α s1 s2 ⟩

@[simp] theorem intersection_self
  {α : Type u} [t : has_belong α] [s : has_intersection α α] {a : α} :
a ∩ a = a :=
by
  rw [← extensionality_belong];
  intro x;
  erw [has_intersection.proof_intersection]
  rw [and_self];

-- @[simp]
-- theorem union_intersection_left_dist
--   {α : Type u} [s : has_binary_union α] [t : has_intersection α α] {a b c : α} :
-- a ∪ (b ∩ c) = (a ∪ b) ∩ (a ∪ c) :=
-- by
--   rw [← extensionality_belong];
--   intro x;
--   erw [has_intersection.proof_intersection];
--   apply Iff.intro <;> intro h;
--   erw [has_binary_union.proof_union] at h;

section succ
open Classical
noncomputable def succ_set (a : set) : set := a ∪ s{a}
theorem belong_succ_iff {a b : set} :
a ∈ succ_set b ↔ a ∈ b ∨ a = b :=
by
  erw [has_binary_union.proof_union];
  rw [@element_in_one_element_set];
theorem self_belong_succ {a : set} : a ∈ succ_set a := by
  rw [belong_succ_iff]; simp;
noncomputable def pred_set (a : set) : set :=
  if h : (∃ b, a = succ_set b) then Classical.choose h else s0

end succ

def subseteq
  {α : Type u} {β : Type v} [s : has_belong α] [t : has_belong β] (a : α) (b : β) : Prop :=
∀ x : set, x ∈ a → x ∈ b
infix:50 " s⊆ " => subseteq
infix:50 " s⊇ " => fun x y => subseteq y x

def subset
  {α : Type u} [s : has_belong α] (a b : α) : Prop :=
a s⊆ b ∧ a ≠ b
infix:50 " s⊂ " => subset
infix:50 " s⊃ " => fun x y => subset y x

@[refl] theorem subseteq_refl
  {α : Type u} [s : has_belong α] {a : α} :
a s⊆ a := by {intro x; apply id}
@[trans] theorem subseteq_trans [has_belong α] [has_belong β]
  [has_belong γ] {a : α} {b : β} {c : γ} :
a s⊆ b → b s⊆ c → a s⊆ c :=
by
  intro h1 h2 x;
  exact fun hp => (h2 x) (h1 x hp);
theorem subseteq_antisymm
  {α : Type u} [s : has_belong α] {a b : α} :
a s⊆ b → b s⊆ a → a = b :=
by
  intros h1 h2;
  rw [← extensionality_belong];
  intro x;
  apply Iff.intro;
  · exact h1 x;
  exact h2 x;

theorem subset_iff_subseteq_not_subseteq
  {α : Type u} [s : has_belong α] {a b : α} :
a s⊂ b ↔ a s⊆ b ∧ ¬b s⊆ a :=
by
  unfold subset;
  apply Iff.intro <;> intro h;
  · rcases h with ⟨h1, h2⟩;
    constructor;
    · exact h1;
    intro h3;
    exact h2 (subseteq_antisymm h1 h3);
  constructor;
  · exact h.1;
  intro h3;
  rw [h3] at h;
  exact h.2 h.1;

-- instance subseteq_is_le {α : Type u} [s : has_belong α] : LE α :=
--   ⟨subseteq⟩
-- instance subset_is_lt {α : Type u} [s : has_belong α] : LT α :=
--   ⟨subset⟩
-- instance subseteq_is_preorder {α : Type u} [s : has_belong α] : Preorder α :=
--   ⟨@subseteq_refl α s, @subseteq_trans α α α s s s,
--     @subset_iff_subseteq_not_subseteq α s⟩
-- instance subseteq_is_partial_order
--   {α : Type u} [s : has_belong α]
--   : PartialOrder α :=
--   ⟨@subseteq_antisymm α s⟩

theorem subseteq_iff_subset_eq
  {α : Type u} [has_belong α] [has_binary_union α] {a b : α} :
a s⊆ b ↔ a s⊂ b ∨ a = b :=
by
  apply Iff.intro <;> intro h;
    swap;
    cases h with
    | inl h => exact h.1;
    | inr h => rw [h];
  unfold subset;
  have f := em (a = b);
  cases f;
  · right; assumption;
  left; constructor; assumption';

@[simp] theorem subseteq_iff_eq_union
  {α : Type u} [has_belong α] [has_binary_union α] {a b : α} :
a s⊆ b ↔ b = a ∪ b :=
by
  apply Iff.intro <;> intro h;
  · rw [← extensionality_belong];
    intro x;
    erw [has_binary_union.proof_union];
    rw [Iff.comm];
    rw [or_iff_right_iff_imp];
    exact h x;
  rw [← extensionality_belong] at h;
  intro x;
  have h := h x;
  erw [has_binary_union.proof_union] at h;
  rw [← or_iff_right_iff_imp];
  rw [Iff.comm];
  exact h;

theorem subseteq_iff_eq_intersection [has_belong α] [has_belong β]
  [has_intersection α β] {a : α} {b : β} :
a s⊆ b ↔ a = a ∩ b :=
by
  apply Iff.intro <;> intro h;
  · rw [← extensionality_belong];
    intro x;
    erw [has_intersection.proof_intersection];
    rw [Iff.comm];
    rw [and_iff_left_iff_imp];
    exact h x;
  rw [← extensionality_belong] at h;
  intro x;
  have h := h x;
  erw [has_intersection.proof_intersection] at h;
  rw [← and_iff_left_iff_imp];
  rw [Iff.comm];
  exact h;

theorem intersection_subseteq_left [has_belong α] [has_belong β] [has_intersection α β]
  [has_intersection α α] {a : α} {b : β} : a ∩ b s⊆ a :=
by
  simp only [subseteq_iff_eq_intersection, intersection_comm];
  rw [← intersection_assoc];
  simp;

theorem intersection_subseteq_right
  {α : Type u} [t : has_belong α] [s : has_intersection α α] {a b : α} :
a ∩ b s⊆ b := by {rw [intersection_comm]; exact intersection_subseteq_left}

theorem union_subseteq_left
  {α : Type u} [has_belong α] [has_binary_union α] {a b : α} :
a s⊆ a ∪ b :=
by
  simp only [subseteq_iff_eq_union]
  rw [← binary_union_assoc]
  simp

theorem union_subseteq_right
  {α : Type u} [has_belong α] [has_binary_union α] {a b : α} :
b s⊆ a ∪ b := by {rw [binary_union_comm]; exact union_subseteq_left}

theorem union_subseteq_iff
  {α : Type u} {β : Type v} [has_belong α] [has_binary_union α]
  [has_belong β] {a b : α} {c : β} :
a ∪ b s⊆ c ↔ a s⊆ c ∧ b s⊆ c :=
by
  constructor <;> intro h;
  constructor <;> intro x;
  any_goals
    have h1 := h x;
    erw [has_binary_union.proof_union] at h1;
    erw [or_imp] at h1;
  · exact h1.1;
  · exact h1.2;
  intros x h1;
  erw [has_binary_union.proof_union] at h1;
  exact Or.elim h1 (h.1 x) (h.2 x);

theorem one_element_set_subseteq {α : Type u} [s : has_belong α] {a : set} {b : α} :
s{a} s⊆ b ↔ a ∈ b :=
by
  constructor <;> intro h
  · have h := h a
    apply h
    rw [element_in_one_element_set]
  intro x; rw [element_in_one_element_set]
  intro h2; rwa [← h2] at h

theorem unionset_subseteq [has_belong α] [has_union α] {a : α} {x : set} :
  x ∈ a → x s⊆ ∪(a) := by
  intro h y hy; unfold make_union_reloaded;
  rw [has_union.proof_union]; use x;

axiom power_set (a : set) : set
axiom axiom_of_power {a} : ∀ x : set, x ∈ power_set a ↔ x s⊆ a

notation "P(" a ")" => power_set a

theorem belong_power_set {a} : a ∈ P(a) :=
by {rw [axiom_of_power]}
theorem union_power_set_eq {a} : ∪(P(a)) = a :=
by
  rw [← extensionality_belong]
  intro x
  erw [has_union.proof_union]
  conv =>
    lhs
    congr
    ext
    rw [axiom_of_power]
  apply Iff.intro
  · intro ⟨c, h⟩
    exact h.2 x h.1
  intro h2;
  use a

axiom make_replacement (a : set) (f : set → set → Prop) : set
axiom axiom_of_replacement (a) (f : set → set → Prop) :
  (∀ u v w : set, f u v ∧ f u w → v = w) →
  ∀ y : set, y ∈ make_replacement a f ↔ ∃ x, x ∈ a ∧ f x y

noncomputable def make_separation (a : set) (A : Class) : set :=
make_replacement a (fun x y => A x ∧ x = y)
theorem axiom_of_separation (a : set) (A : Class) :
  ∀ x : set, x ∈ make_separation a A ↔ x ∈ (set.to_Class a) ∩ A :=
by
  intro x
  have h : (∀ u v w : set, (A u ∧ u = v) ∧ (A u ∧ u = w) → v = w)
  intros u v w f
  · exact Eq.trans (Eq.symm f.1.2) f.2.2
  have f := axiom_of_replacement a _ h x
  erw [f]
  erw [has_intersection.proof_intersection]
  apply Iff.intro <;> intro g;
  · rcases g with ⟨b, ⟨h2, ⟨h3, h4⟩⟩⟩;
    rw [h4] at h2 h3;
    exact ⟨ h2, h3 ⟩;
  use x;
  use g.1;
  simp only [and_true];
  exact g.2;

theorem separation_subseteq {a : set} {A : Class} :
  make_separation a A s⊆ a :=
by
  intros x;
  rw [axiom_of_separation _ _ _];
  exact intersection_subseteq_left x;

theorem subseteq_is_set {a : set} {A : Class} :
  A s⊆ a → A.is_set :=
by
  intro h;
  use make_separation a A;
  rw [← extensionality_belong];
  intro x;
  erw [axiom_of_separation];
  erw [@subseteq_iff_eq_intersection _ _ _ _ _ A a.to_Class] at h;
  erw [intersection_comm] at h;
  erw [← h];

noncomputable instance set.to_has_intersection
  : has_intersection set set :=
⟨ fun x y => make_separation x y.to_Class,
  by
    intro a b c;
    have h := axiom_of_separation a b.to_Class;
    erw [h c];
    erw [has_intersection.proof_intersection];
    rfl;
⟩

noncomputable instance set.to_has_intersection_Class
  : has_intersection set Class :=
⟨ fun x y => make_separation x y,
  by
    intro a b c;
    have h := axiom_of_separation a b;
    erw [h c];
    erw [has_intersection.proof_intersection];
    rfl;
⟩

instance intersection_is_idempotent
  {α : Type u} [t : has_belong α] [s : has_intersection α α] :
  @Std.IdempotentOp α intersection :=
  ⟨ @intersection_self α t s ⟩

theorem intersection_right_set {A : Class} {a : set} :
  A ∩ a.to_Class = (a ∩ A).to_Class := by
  rw [←extensionality_belong]; intro x;
  simp only [intersection_def, ←set_belong_set_to_class, And.comm];
theorem intersection_left_set [has_belong α] [has_intersection set α]
  [has_intersection Class α]
  {A : α} {a : set} :
  a.to_Class ∩ A = (a ∩ A).to_Class := by
  rw [←extensionality_belong]; intro x;
  simp only [intersection_def, ←set_belong_set_to_class, And.comm];
theorem intersection_left_to_set {A : Class} {h : A.is_set} {a : set} :
  A.to_set h ∩ a = (A ∩ a).to_set (subseteq_is_set intersection_subseteq_right) := by
  rw [←extensionality_belong]; intro x;
  simp only [intersection_comm, intersection_def, Class_to_set_ext, And.comm];
theorem intersection_right_to_set {A : Class} {h : A.is_set} {a : set} :
  a ∩ A.to_set h = a ∩ A := by
  rw [←extensionality_belong]; intro x;
  simp only [intersection_def, Class_to_set_ext, And.comm];

noncomputable instance set.to_has_sub : Sub set :=
⟨ fun a b => make_separation a (· ∉ b) ⟩

instance Class.to_has_sub : Sub Class :=
⟨ fun A B x => x ∈ A ∧ x ∉ B ⟩

lemma set_sub_is_sub {a b x : set} :
x ∈ a - b ↔ x ∈ a ∧ x ∉ b :=
by
  erw [axiom_of_separation _ _ _];
  erw [has_intersection.proof_intersection];
  rfl;

lemma class_sub_is_sub {a b : Class} {x : set} :
x ∈ a - b ↔ x ∈ a ∧ x ∉ b := by rfl;

theorem Class_sub_empty_iff_subseteq {A B : Class} : A - B = s0 ↔ A s⊆ B :=
by
  constructor <;> intro h;
  · intro x;
    rw [← extensionality_belong] at h;
    have h := h x;
    erw [empty_false] at h;
    simp only [iff_false] at h;
    erw [not_and_not_right] at h;
    assumption;
  rw [← extensionality_belong]; intro x;
  erw [empty_false];
  simp only [iff_false];
  erw [not_and_not_right];
  exact h x;

@[simp] theorem set_sub_self {a : set} : a - a = s0 :=
by
  rw [← extensionality_belong];
  intro x;
  rw [set_sub_is_sub];
  simp only [and_not_self, false_iff];
  exact axiom_of_empty;

theorem subset_sub_nonempty {A B : Class} :
B s⊂ A → A - B ≠ s0 :=
by
  intro ⟨h1, h2⟩;
  rw [nonempty_class_iff_has_element];
  have h2 : ¬(B = A) := h2;
  erw [← extensionality_belong] at h2;
  push Not at h2; rcases h2 with ⟨x, h2⟩;
  use x; unfold_projs; simp only;
  cases h2 with
  | inr h2 => apply And.symm; assumption;
  | inl h2 =>
    have h1 := h1 x;
    exfalso; exact h2.2 (h1 h2.1);

axiom axiom_of_regularity {a} (h : a ≠ s0) :
∃ x, x ∈ a ∧ x ∩ a = s0

axiom axiom_of_regularity_strong {a : Class} (h : a ≠ s0) :
∃ x, x ∈ a ∧ x ∩ a = s0

theorem belong_to_6 {a1 a2 a3 a4 a5 a6 : set} : ¬(a1 ∈ a2 ∧ a2 ∈ a3 ∧ a3 ∈ a4 ∧
  a4 ∈ a5 ∧ a5 ∈ a6 ∧ a6 ∈ a1) :=
by
  have h : s{a1, a2} ∪ s{a3, a4} ∪ s{a5, a6} ≠ s0;
  · rw [nonempty_iff_has_element];
    use a1;
    repeat erw [has_binary_union.proof_union];
    simp;
  have h := axiom_of_regularity h;
  intro g;
  suffices f : ¬(∃ (x : set), x ∈ s{a1, a2} ∪ s{a3, a4} ∪ s{a5, a6} ∧
      x ∩ (s{a1, a2} ∪ s{a3, a4} ∪ s{a5, a6}) = s0);
    · exact f h;
  push Not;
  intros x f;
  erw [has_binary_union.proof_union, has_binary_union.proof_union] at f;
  rw [axiom_of_pair, axiom_of_pair, axiom_of_pair] at f;
  cases' f with f f; cases' f with f f;
  all_goals cases' f with f f;
  all_goals
    intro h1;
    rw [f] at *;
    rw [← extensionality_belong] at h1;
  have h1 := h1 a6; rotate_left;
  have h1 := h1 a1; rotate_left;
  have h1 := h1 a2; rotate_left;
  have h1 := h1 a3; rotate_left;
  have h1 := h1 a4; rotate_left;
  have h1 := h1 a5; rotate_left;
  all_goals
    erw [has_intersection.proof_intersection] at h1;
    rw [empty_false] at h1;
    simp only [binary_union_assoc, iff_false, not_and] at h1;
  apply h1 g.2.2.2.2.2; rotate_left;
  apply h1 g.1; rotate_left;
  apply h1 g.2.1; rotate_left;
  apply h1 g.2.2.1; rotate_left;
  apply h1 g.2.2.2.1; rotate_left;
  apply h1 g.2.2.2.2.1; rotate_left;
  all_goals {
    repeat erw [has_binary_union.proof_union];
    simp;
  };

theorem belong_to_3 {a b c : set} : a ∈ b → b ∈ c → c ∈ a → False :=
by
  intro h1 h2 h3;
  have f := @belong_to_6 a b c a b c;
  simp only [not_and] at f;
  exact f h1 h2 h3 h1 h2 h3;

theorem belong_to_2 {a b : set} : a ∈ b → b ∈ a → False :=
by
  intro h1 h2;
  have f := @belong_to_6 a b a b a b;
  simp only [not_and] at f;
  exact f h1 h2 h1 h2 h1 h2;

theorem belong_to_self {a : set} : a ∉ a :=
by
  intro h;
  have f := @belong_to_6 a a a a a a;
  simp at f;
  contradiction;

def V : Class := fun x => x = x
@[simp] theorem set_in_allset_prop {x : set} : V x := by {unfold V; rfl}
@[simp] theorem set_in_allset {x : set} : x ∈ V := by {unfold V; rfl}
theorem allset_proper_class : Class.is_proper V :=
by
  intro ⟨x, h⟩;
  have f : x ∈ x;
  · have g := @set_in_allset x;
    rw [← h] at g;
    exact g;
  exact belong_to_self f;

theorem empty_subseteq
  {α : Type u} [s : has_belong α] {a : α} : s0 s⊆ a :=
by {intros x h; exfalso; exact axiom_of_empty h}

theorem allset_supseteq
  {α : Type u} [s : has_belong α] {a : α} : a s⊆ V :=
by {intros x h; exact set_in_allset}

class has_product (α : Type u) [has_belong α] where
(product : α → α → α)
(proof_product {a b : α} {c : set} :
  c ∈ product a b ↔ ∃ x s∈ a, ∃ y s∈ b, c = s⟨x, y⟩)

def Class.product (A B : Class) : Class :=
fun c => ∃ x s∈ A, ∃ y s∈ B, c = s⟨x, y⟩
noncomputable def set.product (a b : set) : set :=
  make_separation P(P(a ∪ b)) (Class.product a.to_Class b.to_Class)

instance Class.to_has_product : has_product Class :=
⟨ Class.product, by {intros; rfl} ⟩
noncomputable instance set.to_has_product : has_product set :=
⟨ set.product, by {
  intros a b c;
  unfold set.product;
  rw [axiom_of_separation];
  apply Iff.intro <;> intro h;
  · have h := intersection_subseteq_right c h;
    exact h;
  constructor; swap;
  · exact h;
  rcases h with ⟨x, ⟨h1, ⟨y, ⟨h2, h⟩⟩⟩⟩;
  rw [h];
  unfold make_ordered_pair;
  erw [axiom_of_power];
  intros z f;
  rw [axiom_of_pair] at f;
  cases' f with f f <;> rw [f, axiom_of_power] <;> intros d g;
  · rw [element_in_one_element_set] at g;
    rw [g];
    erw [has_binary_union.proof_union];
    left; exact h1;
  rw [axiom_of_pair] at g;
  cases' g with g g <;> rw [g] <;> erw [has_binary_union.proof_union];
  · left; assumption;
  right; assumption;
} ⟩
infixl:75 " × " => has_product.product
postfix:80 "²" => fun a => has_product.product a a

@[simp] lemma pair_in_product
  {α : Type u} [has_belong α] [has_product α] {a b : set} {A B : α} :
s⟨a, b⟩ ∈ A × B ↔ a ∈ A ∧ b ∈ B :=
by
  rw [has_product.proof_product];
  apply Iff.intro <;> intro h;
  · rcases h with ⟨x, ⟨h1, ⟨y, ⟨h2, h⟩⟩⟩⟩;
    simp only [ordered_pair_eq_iff] at h;
    rw [h.1, h.2];
    apply And.intro h1 h2;
  use a; use h.1; use b; use h.2;


def is_relation {α : Type u} [s : has_belong α] (a : α) : Prop :=
a s⊆ V²
def is_unitary {α : Type u} [s : has_belong α] (a : α) : Prop :=
∀ u v w : set, s⟨u, v⟩ ∈ a ∧ s⟨u, w⟩ ∈ a → v = w
def is_function {α : Type u} [s : has_belong α] (a : α) : Prop :=
is_relation a ∧ is_unitary a

notation "Rel(" a ")" => is_relation a
notation "Un(" a ")" => is_unitary a
notation "Fnc(" a ")" => is_function a

theorem relation_to_Class [s : has_belong α] (a : α) :
Rel(a) ↔ Rel(has_belong.to_Class a) :=
by
  apply Iff.intro;
  · intro h x h1;
    unfold belong at h1; unfold_projs at h1;
    unfold set.belonged_to has_belong.belong Class.to_has_belong at h1;
    unfold id id at h1;
    rw [←has_belong.proof_Class] at h1;
    exact h x h1;
  intro h x h1;
  apply h x;
  unfold belong; unfold_projs;
  unfold set.belonged_to has_belong.belong Class.to_has_belong;
  unfold id id;
  rw [←has_belong.proof_Class]; exact h1;
theorem unitary_to_Class [s : has_belong α] (a : α) :
Un(a) ↔ Un(has_belong.to_Class a) :=
by
  apply Iff.intro;
  · intro h u v w ⟨h1, h2⟩;
    unfold belong at h1 h2;
    unfold_projs at h1 h2;
    unfold set.belonged_to has_belong.belong Class.to_has_belong at h1 h2;
    unfold id id at h1 h2;
    rw [←has_belong.proof_Class] at h1 h2;
    exact h u v w ⟨h1, h2⟩;
  intro h u v w ⟨h1, h2⟩;
  apply h u v w;
  unfold belong; unfold_projs;
  unfold set.belonged_to has_belong.belong Class.to_has_belong;
  unfold id id;
  rw [←has_belong.proof_Class, ←has_belong.proof_Class];
  exact ⟨h1, h2⟩;
theorem function_to_Class [s : has_belong α] (a : α) :
Fnc(a) ↔ Fnc(has_belong.to_Class a) :=
by
  unfold is_function; apply and_congr;
  · exact relation_to_Class a;
  exact unitary_to_Class a;

theorem unitary_subset
  {α : Type u} {β : Type v} [s : has_belong α] [t : has_belong β] (a : α) (b : β) :
Un(a) ∧ b s⊆ a → Un(b) :=
by
  intro ⟨h1, h2⟩ u v w f;
  have h3 := h2 s⟨u, v⟩ f.1;
  have h4 := h2 s⟨u, w⟩ f.2;
  exact h1 u v w (And.intro h3 h4)

def restrict
  {α : Type u} {β : Type v} [s : has_belong α] [s2 : has_intersection α Class]
  [t : has_belong β] (a : α) (b : β) : α :=
a ∩ ((has_belong.to_Class b) × V)

noncomputable def set_range (a : set) (A : Class) :=
make_replacement a (fun u v => s⟨u, v⟩ ∈ A)

theorem function_replacement_lemma (a : set) (A : Class) (h : Un(A)) :
∀ y : set, y ∈ make_replacement a (fun u v => s⟨u, v⟩ ∈ A) ↔
∃ x s∈ a, s⟨x, y⟩ ∈ A := (axiom_of_replacement a _ h)

def function_domain : Class := fun a => ∃ x y, a = s⟨s⟨x, y⟩, x⟩
def function_range : Class := fun a => ∃ x y, a = s⟨s⟨x, y⟩, y⟩
def function_inverse : Class := fun a => ∃ x y, a = s⟨s⟨x, y⟩, s⟨y, x⟩⟩
def function_congr : Class := fun a => ∃ x y z, a = s⟨s⟨s⟨x, y⟩, s⟨y, z⟩⟩, s⟨x, z⟩⟩

lemma function_domain_unitary : Un(function_domain) :=
by
  intro u v w ⟨⟨x1, ⟨y1, h1⟩⟩, ⟨x2, ⟨y2, h2⟩⟩⟩;
  rw [ordered_pair_eq_iff] at *;
  rw [h2.1] at h1;
  rw [ordered_pair_eq_iff] at *;
  aesop
lemma function_range_unitary : Un(function_range) :=
by
  intro u v w ⟨⟨x1, ⟨y1, h1⟩⟩, ⟨x2, ⟨y2, h2⟩⟩⟩;
  rw [ordered_pair_eq_iff] at *;
  rcases h1 with ⟨h11, h12⟩;
  rcases h2 with ⟨h21, h22⟩;
  rw [h21] at h11;
  rw [ordered_pair_eq_iff] at *;
  aesop
lemma function_inverse_unitary : Un(function_inverse) :=
by
  intro u v w ⟨⟨x1, ⟨y1, h1⟩⟩, ⟨x2, ⟨y2, h2⟩⟩⟩;
  rw [ordered_pair_eq_iff] at *;
  rw [h2.1] at h1;
  rw [ordered_pair_eq_iff] at *;
  aesop
lemma function_congr_unitary : Un(function_congr) := by
  intro u v w ⟨⟨x1, y1, z1, h1⟩, ⟨x2, y2, z2, h2⟩⟩;
  simp only [ordered_pair_eq_iff] at *;
  rcases h1 with ⟨h1, h3⟩; rcases h2 with ⟨h2, h4⟩;
  subst u v w; simp only [ordered_pair_eq_iff] at *;
  simp_all only [and_self];

class has_function (α : Type u)
[has_belong α] [has_intersection α Class] where
(domain : α → α)
(proof_domain {a : α} : ∀ x : set, x ∈ domain a ↔ ∃ y, s⟨x, y⟩ ∈ a)
(range : α → α)
(proof_range {a : α} : ∀ y : set, y ∈ range a ↔ ∃ x, s⟨x, y⟩ ∈ a)
(inverse : α → α)
(proof_inverse {a : α} : ∀ b : set, b ∈ inverse a ↔ ∃ x y, s⟨x, y⟩ ∈ a ∧ b = s⟨y, x⟩)
(congr : α → α → α)
(proof_congr {f g : α} : ∀ b : set, b ∈ congr f g ↔ ∃ x y z, s⟨x, y⟩ ∈ f ∧
  s⟨y, z⟩ ∈ g ∧ b = s⟨x, z⟩)

infix:70 " Γ " => restrict
notation "D(" a ")" => has_function.domain a
notation "W(" a ")" => has_function.range a
notation a "[" b "]" => W(a Γ b)
postfix:80 "⁻¹" => has_function.inverse
def is_one_one {α : Type u} [has_belong α] [has_intersection α Class]
[has_function α] (a : α) : Prop :=
Un(a) ∧ Un(a⁻¹)
notation "Un₂(" a ")" => is_one_one a
def is_one_one_function {α : Type u} [has_belong α] [has_intersection α Class]
[has_function α] (a : α) : Prop :=
Rel(a) ∧ Un₂(a)
notation "Fnc₂(" a ")" => is_one_one_function a
infixr:90 " ∘ " => has_function.congr

theorem inverse_is_relation {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {a : α} : Rel(a⁻¹) :=
by
  intros x h;
  erw [has_function.proof_inverse] at h;
  rcases h with ⟨x1, ⟨y, h⟩⟩;
  rw [h.2, pair_in_product];
  constructor; all_goals {exact set_in_allset};

theorem pair_in_inverse {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {a : α} {x y : set} :
s⟨x, y⟩ ∈ a⁻¹ ↔ s⟨y, x⟩ ∈ a :=
by
  rw [has_function.proof_inverse]; simp;

theorem subset_unitary [has_belong α] [has_intersection α Class] [has_function α]
{f g : α} (h : Un(f)) (h1 : g s⊆ f) : Un(g) :=
  fun u v w ⟨h2, h3⟩ => h u v w ⟨h1 _ h2, h1 _ h3⟩

theorem inv_inv_subset {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f : α} : f⁻¹⁻¹ s⊆ f := by
  intro c; rw [has_function.proof_inverse];
  conv => lhs; rhs; ext; rhs; ext; rw [pair_in_inverse];
  intro ⟨_, _, _, _⟩; subst c; assumption;
theorem rel_inv_inv_eq {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f : α} : Rel(f) → f⁻¹⁻¹ = f := by
  intro h; rw [←extensionality_belong]; intro a;
  use inv_inv_subset _; intro h1;
  rw [has_function.proof_inverse]; have h := h a h1; simp only at h;
  unfold has_product.product Class.to_has_product id at h;
  unfold Class.product at h; rw [proof_in_Class] at h;
  simp only [set_in_allset, true_and] at h;
  rcases h with ⟨y, x, h⟩; use x; use y;
  rw [has_function.proof_inverse];
  simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and, exists_eq_right'];
  rw [← h]; use h1;
theorem domain_inv {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f : α} : D(f⁻¹) = W(f) := by
  rw [←extensionality_belong]; intro a;
  rw [has_function.proof_domain, has_function.proof_range];
  conv => lhs; rhs; ext; rw [pair_in_inverse];
theorem range_inv {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f : α} : W(f⁻¹) = D(f) := by
  rw [←extensionality_belong]; intro a;
  rw [has_function.proof_domain, has_function.proof_range];
  conv => lhs; rhs; ext; rw [pair_in_inverse];
theorem inv_unitary2 [has_belong α] [has_intersection α Class] [has_function α]
{f : α} (h : Un₂(f)) : Un₂(f⁻¹) := ⟨h.2, subset_unitary h.1 inv_inv_subset⟩
theorem congr_unitary [has_belong α] [has_intersection α Class] [has_function α]
  {f g : α} (h1 : Un(f)) (h2 : Un(g)) : Un(f ∘ g) := by
  intro u v w ⟨hu, hv⟩; rw [has_function.proof_congr] at *;
  rcases hu with ⟨x1, y1, z1, hu1, hu2, hu3⟩;
  rcases hv with ⟨x2, y2, z2, hv1, hv2, hv3⟩; simp only [ordered_pair_eq_iff] at *;
  rcases hu3 with ⟨_, _⟩; rcases hv3 with ⟨_, _⟩; subst u v w x1;
  have h3 := h1 x2 y1 y2 ⟨hu1, hv1⟩; subst y1;
  exact h2 y2 z1 z2 ⟨hu2, hv2⟩;
theorem congr_relation [has_belong α] [has_intersection α Class] [has_function α]
  {f g : α} : Rel(f ∘ g) := by
  intro c hc; rw [has_function.proof_congr] at hc;
  rcases hc with ⟨_, _, _, _, _, _⟩; subst c; simp;
theorem congr_inv [has_belong α] [has_intersection α Class] [has_function α]
  {f g : α} : (f ∘ g)⁻¹ = (g⁻¹) ∘ (f⁻¹) := by
  rw [←extensionality_belong]; intro a;
  rw [has_function.proof_inverse, has_function.proof_congr];
  conv => lhs; rhs; ext; rhs; ext; rw [has_function.proof_congr]; simp;
  conv =>
    rhs; rhs; ext; rhs; ext; rhs; ext;
    rw [has_function.proof_inverse, has_function.proof_inverse]; simp;
  simp only [exists_and_left]; constructor <;> intro ⟨a1, b, c, d⟩;
  · rcases c with ⟨c, e, f1⟩; subst a;
    simp only [ordered_pair_eq_iff, exists_eq_right_right', ↓existsAndEq, and_true];
    use c;
  · rcases d with ⟨d, e, f1⟩; subst a;
    simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and, exists_eq_right'];
    use b;
theorem congr_unitary2 [has_belong α] [has_intersection α Class] [has_function α]
  {f g : α} (h1 : Un₂(f)) (h2 : Un₂(g)) : Un₂(f ∘ g) := by
  use congr_unitary h1.1 h2.1; rw [congr_inv]; apply congr_unitary h2.2 h1.2;

theorem belong_restrict {α : Type u} [has_belong α] [has_intersection α Class]
  {β : Type v} [has_belong β] {F : α} {a : β} {b : set} :
  b ∈ F Γ a ↔ b ∈ F ∧ ∃ x s∈ a, ∃ y, b = s⟨x, y⟩ :=
by
  erw [has_intersection.proof_intersection];
  simp only [and_congr_right_iff];
  intro h; rw [has_product.proof_product];
  constructor <;> intro h₀;
  · rcases h₀ with ⟨x, h₁, y, h₂, h₀⟩;
    use x; unfold belong at h₁; unfold_projs at h₁;
    unfold set.belonged_to at h₁; unfold_projs at h₁;
    unfold id at h₁;
    erw [←has_belong.proof_Class] at h₁; use h₁;
    use y;
  simp only [set_in_allset, true_and];
  conv =>
    rhs; ext; lhs; erw [proof_to_Class];
  exact h₀;

theorem congr_image [has_belong α] [has_intersection α Class] [has_function α]
  [has_belong β] {f g : α} {a : β} : (f ∘ g)[a] = g[f[a]] := by
  rw [←extensionality_belong]; intro x;
  simp only [has_function.proof_range, belong_restrict, has_function.proof_congr];
  simp only [ordered_pair_eq_iff, exists_and_left, ↓existsAndEq, and_true, exists_eq_right'];
  aesop;

@[simp] theorem pair_in_restrict {α : Type u} [has_belong α] [has_intersection α Class]
  {β : Type v} [has_belong β] {F : α} {a : β} {x y : set} :
  s⟨x, y⟩ ∈ F Γ a ↔ s⟨x, y⟩ ∈ F ∧ x ∈ a :=
by
  rw [belong_restrict]; simp;
@[simp] theorem pair_in_congr [has_belong α] [has_intersection α Class]
  [has_function α] {f g : α} {x y : set} :
  s⟨x, y⟩ ∈ (f ∘ g) ↔ ∃ z, s⟨x, z⟩ ∈ f ∧ s⟨z, y⟩ ∈ g := by
  rw [has_function.proof_congr]; simp;

theorem one_one_function_iff_func {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {a : α} : Fnc₂(a) ↔ Fnc(a) ∧ Fnc(a⁻¹) :=
by
  unfold is_one_one_function is_one_one is_function;
  conv =>
    rhs; congr; skip;
    conv =>
      congr; simp [inverse_is_relation];
    simp;
  rw [and_assoc];
  simp only [and_congr_right_iff, iff_and_self];
  intros; exact inverse_is_relation;

theorem inverse_image {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f a : α} (h : Un₂(f))
  (h2 : a s⊆ D(f)) : f⁻¹[f[a]] = a :=
by
  rw [← extensionality_belong]; intro x;
  rw [has_function.proof_range];
  constructor <;> intro g;
  · rcases g with ⟨y, g⟩;
    rw [pair_in_restrict] at g; rcases g with ⟨g1, g2⟩;
    rw [has_function.proof_range] at g2;
    rcases g2 with ⟨z, g2⟩;
    rw [pair_in_restrict] at g2; rcases g2 with ⟨g2, g3⟩;
    rw [←pair_in_inverse] at g2;
    suffices h1 : x = z;
    · subst z; use g3;
    apply h.2; use g1;
  have h2 := h2 x g; rw [has_function.proof_domain] at h2;
  rcases h2 with ⟨y, h2⟩; use y;
  rw [pair_in_restrict, pair_in_inverse]; use h2;
  rw [has_function.proof_range]; use x; rw [pair_in_restrict];
  use h2;

theorem relation_restrict {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f : α}
  {β : Type v} [has_belong β] {a : β} : Rel(f Γ a) := by
  intro c hc; rw [belong_restrict] at hc;
  rcases hc with ⟨_, _, _, _, _⟩; subst c; simp;
theorem unitary_restrict {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f : α}
  {β : Type v} [has_belong β] {a : β}
  (h : Un(f)) : Un(f Γ a) :=
by
  intros u v w g;
  rw [pair_in_restrict, pair_in_restrict] at g;
  rcases g with ⟨⟨h1, h2⟩, h3, h4⟩; apply h;
  use h1;
theorem one_one_restrict {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {f : α}
  {β : Type v} [has_belong β] {a : β}
  (h : Un₂(f)) : Un₂(f Γ a) := by
  use unitary_restrict h.1; intro u v w ⟨h1, h2⟩;
  have h3 := h.2 u v w;
  rw [pair_in_inverse] at *; rw [pair_in_inverse] at h3;
  exact h3 ⟨(pair_in_restrict.1 h1).1, (pair_in_restrict.1 h2).1⟩

theorem set_function_domain {a : set} (x : set) :
x ∈ set_range a function_domain ↔ ∃ (y : set), s⟨x, y⟩ ∈ a :=
by
  erw [function_replacement_lemma];
  apply Iff.intro <;> intro h;
  · rcases h with ⟨x1, ⟨h1, ⟨x2, ⟨y, h⟩⟩⟩⟩;
    erw [ordered_pair_eq_iff] at h;
    use y; rwa [h.1, ← h.2] at h1;
  · rcases h with ⟨y, h⟩;
    use s⟨x, y⟩; use h;
    use x; use y;
  exact function_domain_unitary;
theorem set_function_range {a : set} (y : set) :
y ∈ set_range a function_range ↔ ∃ (x : set), s⟨x, y⟩ ∈ a :=
by
  erw [function_replacement_lemma];
  apply Iff.intro <;> intro h;
  · rcases h with ⟨x1, ⟨h1, ⟨x2, ⟨y, h⟩⟩⟩⟩;
    erw [ordered_pair_eq_iff] at h;
    use x2; rwa [h.1, ← h.2] at h1;
  · rcases h with ⟨y1, h⟩;
    use s⟨y1, y⟩; use h;
    use y1; use y;
  exact function_range_unitary;
theorem set_function_inverse {a : set} (b : set) :
b ∈ set_range a function_inverse ↔ ∃ x y, s⟨x, y⟩ ∈ a ∧ b = s⟨y, x⟩ :=
by
  erw [function_replacement_lemma];
  apply Iff.intro <;> intro h;
  · rcases h with ⟨x1, ⟨h1, ⟨x2, ⟨y, h⟩⟩⟩⟩;
    erw [ordered_pair_eq_iff] at h;
    use x2; rw [h.1] at h1;
    rcases h with ⟨h3, h4⟩;
    constructor; constructor; any_goals assumption;
  · rcases h with ⟨y1, ⟨y2, h⟩⟩;
    use s⟨y1, y2⟩; use h.1;
    use y1; use y2; rw [h.2];
  exact function_inverse_unitary
theorem set_function_congr {f g : set} (b : set) :
  b ∈ set_range (f × g) function_congr ↔
  ∃ x y z, s⟨x, y⟩ ∈ f ∧ s⟨y, z⟩ ∈ g ∧ b = s⟨x, z⟩ := by
  erw [function_replacement_lemma];
  apply Iff.intro <;> intro h;
  · rcases h with ⟨x1, h1, x2, y, z, h2⟩;
    simp only [ordered_pair_eq_iff] at h2; rcases h2 with ⟨h2, h3⟩; subst x1 b;
    rw [pair_in_product] at h1; use x2; use y; use z;
    use h1.1; use h1.2;
  · rcases h with ⟨x, y, z, h1, h2, h3⟩; subst b;
    use s⟨s⟨x, y⟩, s⟨y, z⟩⟩; rw [pair_in_product];
    use ⟨h1, h2⟩; use x; use y; use z;
  exact function_congr_unitary

noncomputable instance set.to_has_function : has_function set :=
⟨
  fun a => set_range a function_domain,
  @set_function_domain,
  fun a => set_range a function_range,
  @set_function_range,
  fun a => set_range a function_inverse,
  @set_function_inverse,
  fun a b => set_range (a × b) function_congr,
  @set_function_congr,
⟩

instance Class.to_has_function : has_function Class :=
{
  domain := fun A x => ∃ y, s⟨x, y⟩ ∈ A,
  proof_domain := by {intros; rfl},
  range := fun A y => ∃ x, s⟨x, y⟩ ∈ A,
  proof_range := by {intros; rfl},
  inverse := fun A b => ∃ x y, s⟨x, y⟩ ∈ A ∧ b = s⟨y, x⟩,
  proof_inverse := by {intros; rfl}
  congr := fun F G b => ∃ x y z, s⟨x, y⟩ ∈ F ∧ s⟨y, z⟩ ∈ G ∧ b = s⟨x, z⟩
  proof_congr := by {intros; rfl}
}

theorem unitary2_to_Class [has_belong α] [has_intersection α Class]
  [has_function α] (a : α) :
  Un₂(a) ↔ Un₂(has_belong.to_Class a) := by
  constructor <;> intro h;
  use (unitary_to_Class a).1 h.1; swap; use (unitary_to_Class a).2 h.1;
  all_goals
    intro u v w ⟨hv, hw⟩;
    have h2 := h.2 u v w; rw [pair_in_inverse] at hv hw h2;
  rw [←proof_to_Class] at hv hw; swap; rw [proof_to_Class] at hv hw;
  all_goals rw [pair_in_inverse] at h2; exact h2 ⟨hv, hw⟩;

theorem relation_binary_union_is_relation
  {α : Type u} [has_belong α] [has_binary_union α] (a b : α) :
Rel(a) ∧ Rel(b) → Rel(a ∪ b) :=
by
  intros h x f;
  erw [has_binary_union.proof_union] at f;
  cases f with
  | inl f => exact h.1 x f;
  | inr f => exact h.2 x f;

theorem relation_union_is_relation
  {α : Type u} [has_belong α] [has_union α] (a : α) :
(∀ x : set, x ∈ a → Rel(x)) → Rel(∪(a)) :=
by
  intros h x f;
  erw [has_union.proof_union] at f;
  rcases f with ⟨c, f⟩;
  exact h c f.2 x f.1;

theorem union_unitary [has_belong α] [has_intersection α Class]
[has_function α] [has_binary_union α] [has_intersection α α] {a : α} {b : α} :
Un(a) → Un(b) → has_belong.to_Class (D(a) ∩ D(b)) = ↑s0 → Un(a ∪ b) :=
by
  intro r1 r2 h x y z ⟨hy, hz⟩;
  simp only [binary_union_def] at hy hz;
  cases hy with
  | inl hy =>
    cases hz with
    | inl hz => exact r1 x y z ⟨hy, hz⟩;
    | inr hz =>
      have h1 := fun a =>
        exists_imp.1 ((@has_function.proof_domain α _ _ _ a x).2);
      have hy := h1 a _ hy; have hz := h1 b _ hz;
      have h2 := has_intersection.proof_intersection.2 ⟨hy, hz⟩;
      rw [←proof_to_Class] at h2;
      erw [h] at h2; erw [empty_false] at h2; contradiction;
  | inr hy =>
    cases hz with
    | inl hz =>
      have h1 := fun a =>
        exists_imp.1 ((@has_function.proof_domain α _ _ _ a x).2);
      have hz := h1 a _ hz; have hy := h1 b _ hy;
      have h2 := has_intersection.proof_intersection.2 ⟨hz, hy⟩;
      rw [←proof_to_Class] at h2;
      erw [h] at h2; erw [empty_false] at h2; contradiction;
    | inr hz => exact r2 x y z ⟨hy, hz⟩;

theorem union_function [has_belong α] [has_intersection α Class]
[has_function α] [has_binary_union α] [has_intersection α α] {a : α} {b : α} :
Fnc(a) → Fnc(b) → has_belong.to_Class (D(a) ∩ D(b)) = ↑s0 → Fnc(a ∪ b) := by
  intro fa fb h;
  exact ⟨relation_binary_union_is_relation _ _ ⟨fa.1, fb.1⟩,
    union_unitary fa.2 fb.2 h⟩

theorem function_replacement (a : set) (A : Class) (h : Un(A)) :
(A[a]).is_set :=
by
  have g := function_replacement_lemma a A h;
  use make_replacement a (fun (u v : set) => s⟨u, v⟩ ∈ A);
  rw [← extensionality_belong];
  intro y;
  erw [g y];
  apply Iff.intro <;> intro f;
  · rcases f with ⟨x, ⟨hf, f⟩⟩;
    rw [has_function.proof_range]; use x;
    erw [has_intersection.proof_intersection]; use f;
    rw [pair_in_product];
    constructor;
    · exact hf;
    exact set_in_allset;
  rw [has_function.proof_range] at f;
  rcases f with ⟨x, f⟩;
  use x;
  erw [has_intersection.proof_intersection] at f;
  rw [pair_in_product] at f;
  constructor;
  · exact f.2.1;
  exact f.1;

lemma range_is_restrict {α : Type u} [has_belong α]
[has_intersection α Class] [has_function α] {a : α} :
a[D(a)] = W(a) :=
by
  rw [← extensionality_belong];
  intro x;
  erw [has_function.proof_range];
  erw [has_function.proof_range];
  apply Iff.intro <;>
    intro h <;>
    rcases h with ⟨y, h⟩ <;>
    use y <;>
    erw [has_intersection.proof_intersection] at *;
  · exact h.1;
  use h;
  rw [pair_in_product];
  unfold belong; unfold_projs; unfold set.belonged_to;
  unfold_projs; unfold id;
  erw [← has_belong.proof_Class];
  simp only [set_in_allset_prop, and_true];
  have f : y ∈ D(a); swap; · exact f;
  erw [has_function.proof_domain];
  use x;

theorem proper_class_set_product_proper {A : Class} {B : set} :
A.is_proper ∧ B ≠ s0 → (A × B).is_proper :=
by
  intro ⟨h1, h2⟩;
  rw [nonempty_iff_has_element] at h2;
  rcases h2 with ⟨b, h2⟩;
  intro ⟨a, f⟩;
  have g : Un(function_domain ∩ (A × s{b}) × A);
  · refine unitary_subset _ _ (And.intro function_domain_unitary
    intersection_subseteq_left);
  have h : D(function_domain ∩ (A × s{b}) × A) s⊆ A × B;
  intros x h3;
  · rw [has_function.proof_domain] at h3;
    rcases h3 with ⟨y, h3⟩;
    erw [has_intersection.proof_intersection] at h3;
    rcases h3 with ⟨⟨x1, ⟨y2, h3⟩⟩, h4⟩;
    rw [pair_in_product] at h4;
    simp only [ordered_pair_eq_iff] at h3;
    rcases h4 with ⟨h5, h6⟩;
    rw [h3.1, pair_in_product] at h5;
    rcases h5 with ⟨h5, h6⟩;
    erw [element_in_one_element_set] at h6;
    rw [h3.1, pair_in_product, h6];
    exact And.intro h5 h2;
  rw [← f] at h;
  have h := subseteq_is_set h;
  rcases h with ⟨x, h⟩;
  have h3 : W(function_domain ∩ A × ↑s{b} × A) = A;
  · rw [← extensionality_belong];
    intros x1;
    rw [has_function.proof_range];
    apply Iff.intro <;> intro h4;
    · rcases h4 with ⟨x2, h4⟩;
      erw [has_intersection.proof_intersection] at h4;
      rw [pair_in_product] at h4;
      exact h4.2.2;
    use s⟨x1, b⟩;
    erw [has_intersection.proof_intersection];
    constructor;
    · use x1; use b;
    repeat rw [pair_in_product];
    simp only [h4, true_and, and_true];
    erw [element_in_one_element_set];
  rw [← range_is_restrict] at h3;
  rw [← h] at h3;
  have h4 := function_replacement x _ g;
  rcases h4 with ⟨x2, h4⟩;
  erw [← h4] at h3;
  unfold Class.is_proper at h1;
  unfold Class.is_set at h1;
  push Not at h1;
  exact h1 x2 h3;

postfix:max "&" => fun {β} [has_belong β] (R : β) (x y) => s⟨x, y⟩ ∈ R

def value_class (A : Class) (b : set) : Class :=
fun x => ∃ y : set, x ∈ y ∧ s⟨b, y⟩ ∈ A ∧ ∀ y2, s⟨b, y2⟩ ∈ A → y = y2

theorem value_class_case1 {A : Class} {b y : set} {g : s⟨b, y⟩ ∈ A}
{h : ∃!y, s⟨b, y⟩ ∈ A} : ∀ x : set, x ∈ value_class A b ↔ x ∈ y :=
by
  rcases h with ⟨x, h₁, h₂⟩; intro a;
  have hxy : y = x;
  · apply h₂; assumption;
  subst x; constructor <;> intro ha; swap;
  · use y; use ha; use h₁;
    intros z hy; symm; apply h₂; use hy;
  rcases ha with ⟨z, h₃, h₄, h₅⟩;
  suffices hyz : z = y; · rwa [←hyz];
  apply h₅; assumption;

theorem value_class_case2 {A : Class} {b : set} {h : ¬∃!y, s⟨b, y⟩ ∈ A} :
value_class A b = s0 :=
by
  rw [←extensionality_belong]; intro a; erw [empty_false];
  simp only [iff_false];
  intro h₁; unfold ExistsUnique at h; push Not at h;
  rcases h₁ with ⟨y, h₁, h₂, h₃⟩;
  obtain ⟨h₄, h₅, h₆⟩ := h y h₂;
  apply h₆; symm; apply h₃; assumption;

theorem value_class_is_set {A : Class} {b : set} : (value_class A b).is_set :=
by
  have h := em (∃!y, s⟨b, y⟩ ∈ A);
  cases h with
  | inl h =>
    rcases h with ⟨x, h₁, h₂⟩;
    use x; rw [←extensionality_belong]; intro a;
    rw [Iff.comm];
    apply value_class_case1; · assumption;
    use x;
  | inr h =>
    rw [value_class_case2];
    · exact set_to_Class_is_set;
    assumption;

noncomputable def value (A : Class) (b : set) : set :=
(value_class A b).to_set value_class_is_set
class has_value (α : Type u) [has_belong α] [has_intersection α Class]
  extends has_function α where
(value : α → set → set)
(value_case1 {A : α} {b y : set} : s⟨b, y⟩ ∈ A →
  (∃!y, s⟨b, y⟩ ∈ A) -> value A b = y
)
(value_case2 {A : α} {b : set} :
  (¬∃!y, s⟨b, y⟩ ∈ A) -> value A b = s0)

theorem value_case1_ {A : Class} {b y : set} (g : s⟨b, y⟩ ∈ A)
(h : ∃!y, s⟨b, y⟩ ∈ A) : value A b = y :=
by
  rw [←extensionality_belong]; intro a;
  unfold value; rw [Class_to_set_ext];
  apply value_class_case1; assumption';

theorem value_case2_ {A : Class} {b : set} (h : ¬∃!y, s⟨b, y⟩ ∈ A) :
value A b = s0 :=
by
  rw [←extensionality_belong]; intro a;
  rw [empty_false]; simp only [iff_false];
  unfold value; rw [Class_to_set_ext];
  rw [value_class_case2];
  · erw [empty_false]; trivial;
  assumption

noncomputable instance Class.to_has_value : has_value Class :=
⟨
  value, value_case1_, value_case2_
⟩

noncomputable instance set.to_has_value : has_value set :=
⟨
  fun s => value ↑s, by {
    intro A b y h h2; rw [set_belong_set_to_class] at h;
    apply value_case1_ h;
    conv => rhs; ext; rw [←set_belong_set_to_class];
    assumption;
  }, by {
    intro A b h;
    conv at h => rhs; rhs; ext; rw [set_belong_set_to_class];
    apply value_case2_ h;
  }
⟩

notation h "[[" x "]]" => has_value.value h x

theorem value_func [has_belong α] [has_intersection α Class] [has_value α]
{A : α} {b y : set} (h : Un(A)) (g : s⟨b, y⟩ ∈ A) :
A[[b]] = y :=
by
  apply has_value.value_case1; · assumption;
  have h2 := h b y;
  use y; use g; intro w h3;
  symm; apply h2; constructor <;> assumption;

theorem value_func2 [has_belong α] [has_intersection α Class] [has_value α]
{A : α} {b : set} (h : Un(A)) (d : b ∈ D(A)) :
s⟨b, A[[b]]⟩ ∈ A :=
by
  rw [has_function.proof_domain] at d; rcases d with ⟨y, d⟩;
  rwa [value_func h d];

theorem value_func_iff [has_belong α] [has_intersection α Class] [has_value α]
{A : α} {b y : set} (h : Un(A)) : s⟨b, y⟩ ∈ A ↔ (A[[b]] = y ∧ b ∈ D(A)) :=
by
  constructor;
  · intro ha; use value_func h ha; exact (has_function.proof_domain _).2 ⟨_, ha⟩;
  intro ⟨_, _⟩; subst y; apply value_func2 h; assumption;

theorem value_func_un2 [has_belong α] [has_intersection α Class] [has_value α]
{A : α} {b : set} (h : Un₂(A)) (d : b ∈ D(A)) : s⟨a, A[[b]]⟩ ∈ A ↔ a = b :=
by
  constructor <;> intro h1; swap;
  · subst a; exact value_func2 h.1 d;
  have h2 := value_func2 h.1 d; rw [←pair_in_inverse] at h1 h2;
  exact h.2 _ _ _ ⟨h1, h2⟩;

theorem succ_pred_set (a : set) : a = pred_set (succ_set a) := by
  unfold pred_set;
  have h : ∃ b, succ_set a = succ_set b; · use a;
  simp only [h, ↓reduceDIte];
  have h1 := Classical.choose_spec h;
  have h2 := @self_belong_succ a;
  rw [h1, belong_succ_iff] at h2;
  cases h2 with
  | inr => assumption;
  | inl h2 =>
    have h3 := @self_belong_succ (Classical.choose h);
    rw [←h1, belong_succ_iff] at h3;
    cases h3 with
    | inr => symm; assumption;
    | inl h3 => exfalso; exact belong_to_2 h2 h3;

theorem pred_succ_set (a : set) (h : ∃ b, a = succ_set b) :
  a = succ_set (pred_set a) := by
  rcases h with ⟨b, h⟩; rw [h]; congr; exact succ_pred_set _;

end zfset
