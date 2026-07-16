import Mathlib
import Myzfc.zfcset1

namespace zfset

theorem value_in_func {A : Class} {x : set} {g : x ∈ D(A)} {h : Un(A)} :
s⟨x, (A[[x]])⟩ ∈ A :=
by
  rcases g with ⟨y, g⟩; rw [value_func]; assumption';

theorem value_in_func_set {f x : set} {g : x ∈ D(f)} {h : Un(f)} :
s⟨x, (↑f[[x]])⟩ ∈ f :=
by
  rw [has_function.proof_domain] at g;
  rcases g with ⟨y, g⟩; rw [value_func]; assumption';

def is_order [has_belong α] [has_belong β] (R : β) (A : α) : Prop :=
(∀ x s∈ A, ∀ y s∈ A, (R& x y ↔ ¬(x = y ∨ R& y x))) ∧
(∀ x s∈ A, ∀ y s∈ A, ∀ z s∈ A, (R& x y ∧ R& y z → R& x z))
def is_partial_order [has_belong α] [has_belong β] (R : β) (A : α) : Prop :=
(∀ x s∈ A, R& x x) ∧
(∀ x s∈ A, ∀ y s∈ A, R& x y ∧ R& y x → x = y) ∧
(∀ x s∈ A, ∀ y s∈ A, ∀ z s∈ A, (R& x y ∧ R& y z → R& x z))
def is_foundational [has_belong α] [has_belong β] [has_intersection β Class]
  [has_function β] [has_intersection set β] (R : β) (A : α) : Prop :=
(∀ a : set, a s⊆ A ∧ a ≠ s0 → ∃ x s∈ a, a ∩ (R⁻¹[s{x}]) = s0)
def is_well_founded [has_belong α] [has_intersection α Class] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β]
  [has_intersection α β] (R : β) (A : α) : Prop :=
is_foundational R A ∧ (∀ x s∈ A, has_belong.is_set (A ∩ (R⁻¹[s{x}])))
def is_well_order [has_belong α] [has_intersection α Class] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β] (R : β) (A : α) : Prop :=
is_foundational R A ∧ (∀ x s∈ A, ∀ y s∈ A, R& x y ∨ x = y ∨ R& y x)
def is_well_founded_well_order [has_belong α] [has_intersection α Class] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β]
  [has_intersection α β] (R : β) (A : α) : Prop :=
is_well_founded R A ∧ is_well_order R A

def E : Class := fun a => ∃ (x : set) (y : set), x ∈ y ∧ a = s⟨x, y⟩
def I : Class := fun a => ∃ x, a = s⟨x, x⟩

@[simp] theorem E_simp {x y : set} : s⟨x, y⟩ ∈ E ↔ x ∈ y :=
by unfold E; rw [proof_in_Class]; simp;
theorem E_first {x : set} : W(E⁻¹ Γ s{x}) = x := by
  rw [←extensionality_belong]; intro a;
  rw [←set_belong_set_to_class, has_function.proof_range];
  conv => lhs; rhs; ext; rw [pair_in_restrict]; lhs; rw [pair_in_inverse];
  simp;
@[simp] theorem id_simp {x y : set} : s⟨x, y⟩ ∈ I ↔ x = y :=
by
  constructor <;> intro h;
  · rcases h with ⟨c, h⟩; simp at h; aesop;
  rw [h]; use y;

@[simp] theorem id_value {x : set} : I[[x]] = x :=
by
  apply value_case1_; · use x;
  use x; constructor; · use x;
  intros y h; simp at h; aesop;

theorem id_one_one : Fnc₂(I) :=
by
  rw [one_one_function_iff_func];
  constructor; constructor;
  · intro x ⟨y, h⟩; rw [h]; simp [pair_in_product];
  · intro u v w ⟨⟨c₁, h₁⟩, c₂, h₂⟩; simp at *; aesop;
  constructor;
  · intro x ⟨y, y₁, h₁, h₂⟩; rw [h₂]; simp [pair_in_product];
  intro u v w ⟨⟨c₁, y₁, h₁⟩, c₂, y₂, h₂⟩; simp at *; aesop;

def Fnc_on {α : Type u} [has_belong α] [has_intersection α Class]
[has_function α] (A B : α) : Prop :=
Fnc(A) ∧ B = D(A)
def Fnc₂_on {α : Type u} [has_belong α] [has_intersection α Class]
[has_function α] (A B : α) : Prop :=
Fnc₂(A) ∧ B = D(A)
def Fnc_sub {α : Type u} [has_belong α] [has_intersection α Class]
[has_function α] (A B : α) : Prop :=
Fnc(A) ∧ B s⊆ D(A)
theorem Fnc_on_sub {α : Type u} [has_belong α] [has_intersection α Class]
[has_function α] (A B : α) :
Fnc_on A B → Fnc_sub A B := fun ⟨a, b⟩ => ⟨a, by {rw [b]}⟩

notation F " f: " A "-Fnc->" B => (Fnc_on F A) ∧ W(F) s⊆ B
notation F " f: " A "-onto->" B => (Fnc_on F A) ∧ W(F) = B
notation F " f: " A "-1-1->" B => (Fnc₂_on F A) ∧ W(F) s⊆ B
notation F " f: " A "-1-1onto->" B => (Fnc₂_on F A) ∧ W(F) = B

def Isom [has_belong α] [has_belong β] [has_belong γ]
[has_intersection α Class] [has_value α]
(h : α) (R1 : β) (R2 : γ) (A1 A2 : α) : Prop :=
(h f: A1 -1-1onto-> A2) ∧ ∀ x s∈ A1, ∀ y s∈ A1, R1& x y ↔ R2& (h[[x]]) (h[[y]])

theorem Fnc_sub_subseteq [has_belong α] [has_intersection α Class]
[has_function α] {A B C : α}
  (h : Fnc_sub A B) (g : C s⊆ B) : Fnc_sub A C :=
⟨h.1, subseteq_trans g h.2⟩

theorem restrict_eq [has_belong α] [has_intersection α Class]
[has_value α] {F G a : α}
  (hf : Fnc_sub F a) (hg : Fnc_sub G a)
  (h : ∀ x s∈ a, (F[[x]]) = (G[[x]])) :
  F Γ a = G Γ a :=
by
  rw [←extensionality_belong]; intro y;
  rw [belong_restrict, belong_restrict];
  rcases hf with ⟨⟨hf1, hf2⟩, hf3⟩;
  rcases hg with ⟨⟨hg1, hg2⟩, hg3⟩;
  constructor <;> intro h;
  · rcases h with ⟨h₀, x, h₁, z, h⟩;
    subst y;
    have h := h x h₁;
    constructor;
    · have h₀ := value_func hf2 h₀;
      rw [h₀] at h;
      have h₂ := hg3 x h₁;
      rw [has_function.proof_domain] at h₂;
      rcases h₂ with ⟨y₁, h₂⟩;
      rw [value_func hg2 h₂] at h;
      · rw [h]; assumption;
    existsi x; use h₁; existsi z; rfl;
  constructor;
  · rcases h with ⟨h₁, ⟨x, ⟨hx, ⟨y₁, hy⟩⟩⟩⟩;
    subst y;
    have h := h x hx;
    have h₁ := value_func hg2 h₁;
    rw [h₁] at h;
    have h₂ := hf3 x hx;
    rw [has_function.proof_domain] at h₂;
    rcases h₂ with ⟨y₂, h₂⟩;
    have h₃ := value_func hf2 h₂;
    rwa [←h, h₃];
  exact h.2;

theorem domain_is_set {f : Class} (g : Fnc(f)) (h : D(f).is_set)
  : f.is_set :=
by
  let F := (function_domain Γ f)⁻¹;
  have hf : Un(F); intros u v w h0;
  · rw [pair_in_inverse, pair_in_inverse,
      pair_in_restrict, pair_in_restrict] at h0;
    rcases h0 with ⟨⟨⟨x1, y1, h0⟩, h1⟩, ⟨x2, y2, h2⟩, h3⟩;
    simp only [ordered_pair_eq_iff] at *; rcases h0; rcases h2;
    subst v w u x2; simp only [ordered_pair_eq_iff, true_and];
    apply g.2; use h1;
  suffices hg : F[D(f).to_set h] = f;
  · rw [←hg]; apply function_replacement; assumption;
  have h0 : F[D(f).to_set h] = F[D(f)];
  · congr 1; unfold restrict;
    congr 2; unfold_projs;
    erw [Class_to_set_to_Class]; rfl;
  rw [h0]; suffices h2 : D(f) = (function_domain Γ f)[f];
  · rw [h2]; apply inverse_image;
    constructor;
    · exact unitary_restrict function_domain_unitary;
    · use hf;
    intros x h1; have h1 := g.1 _ h1;
    rcases h1 with ⟨x1, _, x2, _, h1⟩; subst x;
    rw [has_function.proof_domain]; use x1;
    rw [pair_in_restrict];
    constructor; · use x1; use x2;
    use h1;
  rw [←extensionality_belong]; intro x;
  rw [has_function.proof_range];
  constructor <;> intro h1 <;> rcases h1 with ⟨x1, h1⟩;
  · use s⟨x, x1⟩; rw [pair_in_restrict, pair_in_restrict];
    constructor; constructor;
    · use x; use x1;
    · use h1;
    use h1;
  rw [pair_in_restrict, pair_in_restrict] at h1;
  rcases h1 with ⟨⟨⟨x2, y, h3⟩, h4⟩, h5⟩;
  simp only [ordered_pair_eq_iff] at h3; cases h3;
  subst x2 x1; use y;
theorem set_to_class_domain {f : set} : D(f.to_Class) = D(f).to_Class := by
  rw [←extensionality_belong]; intro a; rw [←set_belong_set_to_class];
  rw [has_function.proof_domain, has_function.proof_domain];
  conv => lhs; rhs; ext; rw [←set_belong_set_to_class];
theorem class_is_set_domain {f : Class} {h : f.is_set} : D(f).is_set := by
  rw [←@Class_to_set_to_Class f h, set_to_class_domain];
  exact set_to_Class_is_set;
theorem class_to_set_domain {f : Class} {h : f.is_set} :
  D(f.to_set h) = D(f).to_set (@class_is_set_domain f h) := by
  conv => rhs; lhs; congr; rw [←@Class_to_set_to_Class f h];
  conv => rhs; lhs; rw [set_to_class_domain];
  rw [set_to_Class_to_set];
theorem class_to_set_rel {f : Class} {h : f.is_set} :
  Rel(f.to_set h) ↔ Rel(f) := by
  unfold is_relation; unfold subseteq;
  conv => lhs; ext; lhs; rw [Class_to_set_ext];
theorem class_to_set_func {f : Class} {h : f.is_set} :
  Fnc(f.to_set h) ↔ Fnc(f) := by
  unfold is_function; rw [class_to_set_rel]; unfold is_unitary;
  conv => lhs; rhs; ext; ext; ext; rw [Class_to_set_ext, Class_to_set_ext];
theorem class_to_set_func2 {f : Class} {h : f.is_set} :
  Fnc₂(f.to_set h) ↔ Fnc₂(f) := by
  unfold is_one_one_function; rw [class_to_set_rel]; unfold is_one_one is_unitary;
  conv => lhs; rhs; lhs; ext; ext; ext; rw [Class_to_set_ext, Class_to_set_ext];
  conv =>
    lhs; rhs; rhs; ext; ext; ext; rw [pair_in_inverse, pair_in_inverse];
    rw [Class_to_set_ext, Class_to_set_ext];
    rw [←pair_in_inverse]; lhs; rhs; rw [←pair_in_inverse];
theorem set_to_class_range {f : set} : W(f.to_Class) = W(f).to_Class := by
  rw [←extensionality_belong]; intro a; rw [←set_belong_set_to_class];
  rw [has_function.proof_range, has_function.proof_range];
  conv => lhs; rhs; ext; rw [←set_belong_set_to_class];
theorem class_is_set_range {f : Class} {h : f.is_set} : W(f).is_set := by
  rw [←@Class_to_set_to_Class f h, set_to_class_range];
  exact set_to_Class_is_set;
theorem class_to_set_range {f : Class} {h : f.is_set} :
  W(f.to_set h) = W(f).to_set (@class_is_set_range f h) := by
  conv => rhs; lhs; congr; rw [←@Class_to_set_to_Class f h];
  conv => rhs; lhs; rw [set_to_class_range];
  rw [set_to_Class_to_set];

theorem function_one_pair {a b} : Fnc_on s{s⟨a, b⟩} s{a} := by
  constructor; constructor;
  · intro x h; rw [element_in_one_element_set] at h; rw [h]; simp;
  · intro u v w ⟨h1, h2⟩; simp at h1 h2; aesop;
  · rw [←extensionality_belong]; intro a1; simp only [element_in_one_element_set];
    rw [has_function.proof_domain]; apply Iff.intro <;> intro h3;
    · rw [h3]; use b; simp;
    · simp at h3; assumption;
theorem value_one_pair {a b} : s{s⟨a, b⟩}[[a]] = b := by
  apply has_value.value_case1; · simp only [element_in_one_element_set];
  use b; simp;
theorem range_one_pair {a b} : W(s{s⟨a, b⟩}) = s{b} := by
  rw [←extensionality_belong]; intro x;
  simp [has_function.proof_range];

theorem domain_union [has_belong α] [has_binary_union α]
[has_intersection α Class] [has_function α] {f g : α} :
D(f ∪ g) = D(f) ∪ D(g) := by
  rw [←extensionality_belong]; intro a; simp only [binary_union_def];
  simp only [has_function.proof_domain, binary_union_def];
  exact exists_or;
theorem range_union [has_belong α] [has_binary_union α]
[has_intersection α Class] [has_function α] {f g : α} :
W(f ∪ g) = W(f) ∪ W(g) := by
  rw [←extensionality_belong]; intro a; simp only [binary_union_def];
  simp only [has_function.proof_range, binary_union_def];
  exact exists_or;
theorem restrict_union [has_belong α] [has_binary_union α]
[has_intersection α Class] [t : has_belong β]
{f g : α} {x : β} : (f ∪ g) Γ x = (f Γ x) ∪ (g Γ x) := by
  rw [←extensionality_belong]; intro a; unfold restrict;
  simp only [intersection_def, binary_union_def]; exact or_and_right
theorem restrict_to_union [has_belong α] [has_binary_union α]
[has_intersection α Class] [has_belong β] [has_binary_union β]
{f : α} {x y : β} : f Γ (x ∪ y) = (f Γ x) ∪ (f Γ y) := by
  rw [←extensionality_belong]; intro a; unfold restrict;
  simp [intersection_def, binary_union_def, has_product.proof_product]; aesop;

theorem union_function_apply {a b : Class}
(fa : Fnc(a)) (fb : Fnc(b)) (h : (D(a) ∩ D(b)) = ↑s0)
(x : set) (hx : x ∈ D(a)) : (a ∪ b)[[x]] = a[[x]] := by
  have fu := union_function fa fb h; rw [value_func fu.2];
  · simp only [binary_union_def]; left;
    rw [has_function.proof_domain] at hx; rcases hx with ⟨y, hx⟩;
    have hv := value_func fa.2 hx; rwa [hv];

theorem union_function_apply_set {a b : set}
(fa : Fnc(a)) (fb : Fnc(b)) (h : (D(a) ∩ D(b)) = s0)
(x : set) (hx : x ∈ D(a)) : (a ∪ b)[[x]] = a[[x]] := by
  have hu : has_belong.to_Class s0 = ↑s0; · rfl;
  have fu := union_function fa fb; rw [h] at fu;
  have fu := fu hu; rw [value_func fu.2];
  rw [has_function.proof_domain] at hx; rcases hx with ⟨y, hx⟩;
  have hv := value_func fa.2 hx; rw [hv];
  simp only [binary_union_def]; left; assumption;

theorem domain_restrict [has_belong α] [has_intersection α Class]
  [has_function α] [has_belong β] [has_intersection α β] {f : α} {a : β} :
  D(f Γ a) = D(f) ∩ a := by
  rw [←extensionality_belong]; intro x; simp only [intersection_def];
  rw [has_function.proof_domain, has_function.proof_domain];
  conv => lhs; rhs; ext; rw [pair_in_restrict];
  simp only [exists_and_right];

theorem restrict_is_func [has_belong α] [has_intersection α Class]
  [has_function α] [has_belong β] {f : α} {a : β} :
  Fnc(f) → Fnc(f Γ a) := by
  intro h; constructor;
  · intro c hc; rw [belong_restrict] at hc;
    rcases hc with ⟨hl, ⟨x, ⟨hx, ⟨y, hy⟩⟩⟩⟩; rw [hy]; simp;
  · intro u v w ⟨hu, hv⟩; rw [pair_in_restrict] at hu hv;
    exact h.2 u v w ⟨hu.1, hv.1⟩;

theorem restrict_is_set {f : Class} {a : set} (h : Fnc(f)) :
  (f Γ a).is_set := by
  apply domain_is_set; · exact restrict_is_func h;
  rw [domain_restrict]; apply subseteq_is_set; exact intersection_subseteq_right;

theorem domain_empty {f : Class} (h : Fnc_on f ↑s0) :
  f = ↑s0 := by
  rw [←extensionality_belong]; intro x; rw [←set_belong_set_to_class];
  rw [empty_false]; simp only [iff_false]; intro ha;
  have h1 := h.1.1 x ha; rw [has_product.proof_product] at h1;
  simp only [set_in_allset, true_and] at h1;
  rcases h1 with ⟨a, b, h1⟩; rw [h1] at ha;
  have hx := (has_function.proof_domain a).2 ⟨b, ha⟩;
  rw [←h.2, ←set_belong_set_to_class] at hx; exact empty_false.1 hx;
theorem restrict_empty {f : Class} (h : Fnc(f)) : f Γ s0 = s0 := by
  apply domain_empty; use restrict_is_func h;
  rw [domain_restrict, ←extensionality_belong]; intro a;
  simp only [intersection_def];
  rw [←set_belong_set_to_class]; rw [empty_false]; simp;
theorem domain_empty_set {f : set} (h : Fnc_on f s0) :
  f = ↑s0 := by
  rw [←extensionality_belong]; intro x;
  rw [empty_false]; simp only [iff_false]; intro ha;
  have h1 := h.1.1 x ha; rw [has_product.proof_product] at h1;
  simp only [set_in_allset, true_and] at h1;
  rcases h1 with ⟨a, b, h1⟩; rw [h1] at ha;
  have hx := (has_function.proof_domain a).2 ⟨b, ha⟩;
  rw [←h.2] at hx; exact empty_false.1 hx;
theorem restrict_empty_set {f : set} (h : Fnc(f)) : f Γ s0 = s0 := by
  apply domain_empty_set; use restrict_is_func h;
  rw [domain_restrict, ←extensionality_belong]; intro a;
  simp only [intersection_def]; rw [empty_false]; simp;
theorem range_empty_set : W(s0) = s0 := by
  rw [←extensionality_belong]; intro x;
  simp only [empty_false, iff_false];
  rw [has_function.proof_range];
  simp only [empty_false, exists_false, not_false_eq_true];

theorem union_function_restrict [has_belong α] [has_intersection α Class]
  [has_function α] [has_intersection α α] [has_binary_union α]
  [has_intersection α set] {a b : α} (fb : Fnc(b))
(h : has_belong.to_Class (D(a) ∩ D(b)) = ↑s0) (x : set) (hx : ↑x s⊆ D(a)) :
  (a ∪ b) Γ x = a Γ x := by
  rw [←extensionality_belong]; intro y; rw [restrict_union];
  simp only [binary_union_def, or_iff_left_iff_imp]; intro hb;
  exfalso; suffices h1 : has_belong.to_Class (b Γ x) = ↑s0;
  · rw [set_belong_to_class, h1, ←set_belong_set_to_class] at hb; exact empty_false.1 hb;
  apply domain_empty; constructor;
  · rw [←function_to_Class]; exact (restrict_is_func fb);
  rw [←extensionality_belong]; intro c;
  rw [←set_belong_set_to_class]; simp only [empty_false, false_iff];
  rw [has_function.proof_domain];
  conv => rhs; rhs; ext; rw [←set_belong_to_class];
  rw [←has_function.proof_domain];
  rw [domain_restrict]; simp only [intersection_def, not_and];
  intro h2 h1; have hx := hx _ h1;
  have hc := has_intersection.proof_intersection.2 ⟨hx, h2⟩;
  unfold intersection at h; rw [set_belong_to_class] at hc;
  erw [h] at hc; rw [←set_belong_set_to_class] at hc;
  exact empty_false.1 hc;

theorem value_to_Class {f b : set} : f[[b]] = (f.to_Class)[[b]] := by
  by_cases h : (∃!y, s⟨b, y⟩ ∈ f);
  · have he := h.exists; rcases he with ⟨x, he⟩;
    have h1 := has_value.value_case1 he h; rw [h1];
    conv at h => rhs; ext; rw [set_belong_set_to_class];
    rw [set_belong_set_to_class] at he;
    have h1 := has_value.value_case1 he h; rw [h1];
  · have h1 := has_value.value_case2 h; rw [h1];
    conv at h => rhs; rhs; ext; rw [set_belong_set_to_class];
    have h1 := has_value.value_case2 h; rw [h1];

theorem restrict_to_Class {f b : set} (h : ((f.to_Class) Γ b).is_set) :
f Γ b = ((f.to_Class) Γ b).to_set h := by
  rw [←extensionality_belong]; intro a;
  unfold restrict;
  rw [Class_to_set_ext]; simp only [intersection_def];
  rw [←set_belong_set_to_class];
theorem restrict_value [has_belong α] [has_intersection α Class]
  [s : has_value α] [has_belong β] {f : α} {a : β} {x : set} :
  x ∈ a → (f Γ a)[[x]] = f[[x]] := by
  intro h;
  by_cases h1 : ∃!y, s⟨x, y⟩ ∈ f;
  · have h1' := h1; rcases h1' with ⟨y, h2, h3⟩;
    have hc := has_value.value_case1 h2 h1; rw [hc];
    apply has_value.value_case1; · rw [pair_in_restrict]; use h2;
    use y; constructor; · apply pair_in_restrict.2; use h2;
    intro z hz; rw [pair_in_restrict] at hz; exact h3 z hz.1;
  have hc := has_value.value_case2 h1; rw [hc];
  apply has_value.value_case2; intro ⟨y, h2, h3⟩; apply h1;
  use y; simp only at h2 h3; rw [pair_in_restrict] at h2; use h2.1;
  intro z hz; apply h3; rw [pair_in_restrict]; use hz;

theorem restrict_range [has_belong α] [has_intersection α Class]
  [has_function α] [has_belong β] {f : α} {a : β} : W(f Γ a) s⊆ W(f) := by
  intro x; rw [has_function.proof_range, has_function.proof_range];
  simp only [forall_exists_index]; intro y;
  rw [pair_in_restrict]; intro ⟨_, _⟩; use y;
theorem congr_range [has_belong α] [has_intersection α Class] [has_function α]
  {f g : α} : W(f ∘ g) s⊆ W(g) := by
  intro x; rw [has_function.proof_range, has_function.proof_range];
  conv => lhs; rhs; ext; rw [has_function.proof_congr];
  intro ⟨_, _, y, _, h, _, h2⟩; use y; simp only [ordered_pair_eq_iff] at h2;
  rwa [h2.2];
theorem restrict_to_domain [has_belong α] [has_intersection α Class]
  [has_function α] {f : α} (h : Rel(f)) : f = f Γ D(f) := by
  rw [←extensionality_belong]; intro x;
  simp only [belong_restrict, has_function.proof_domain, iff_self_and]; intro h1;
  have h2 := h x h1; rw [has_product.proof_product] at h2;
  simp only [set_in_allset, true_and] at h2; rcases h2 with ⟨y, z, h2⟩;
  subst x; simp only [ordered_pair_eq_iff, exists_and_left, ↓existsAndEq, and_true,
    exists_eq_right']; exact ⟨z, h1⟩;
theorem range_one_element {f a : set} (h : Un(f)) (h2 : a ∈ D(f)) :
  f[s{a}] = s{f[[a]]} := by
  rw [←extensionality_belong]; intro x;
  simp only [has_function.proof_range, pair_in_restrict, element_in_one_element_set,
    exists_eq_right]; constructor;
  · exact fun x => Eq.symm ((value_func_iff h).1 x).1;
  exact fun x ↦ (value_func_iff h).2 ⟨Eq.symm x, h2⟩;

theorem id_isom (R A : Class) : Isom (I Γ A) R R A A :=
by
  constructor; constructor; constructor;
  · use relation_restrict; exact one_one_restrict id_one_one.2;
  · rw [←extensionality_belong]; intro a; rw [has_function.proof_domain];
    conv => rhs; rhs; ext; rw [pair_in_restrict];
    simp;
  · rw [←extensionality_belong]; intro a; rw [has_function.proof_range];
    conv => lhs; rhs; ext; rw [pair_in_restrict];
    simp;
  intros x hx y hy; simp only;
  rw [restrict_value hx, restrict_value hy]; simp only [id_value];

class has_inter (α : Type u) [has_belong α] where
(inter : α → α)
(proof_inter {a : α} : (has_belong.to_Class a = ↑s0 →
  has_belong.to_Class (inter a) = ↑s0) ∧ (
has_belong.to_Class a ≠ ↑s0 → ∀ b : set, b ∈ inter a ↔ ∀ c : set, c ∈ a → b ∈ c))

instance Class.to_has_inter : has_inter Class :=
⟨ fun A b => A ≠ ↑s0 ∧ ∀ c : set, c ∈ A → b ∈ c, by
  intro a; constructor <;> intro h;
  · rw [←extensionality_belong]; intro b;
    rw [←set_belong_to_class, ←set_belong_set_to_class, proof_in_Class];
    simp only [ne_eq, empty_false, iff_false, not_and, not_forall];
    intro a1; contradiction;
  intro b; rw [proof_in_Class]; constructor <;> intro h1;
  · exact h1.2;
  exact ⟨h, h1⟩;
⟩
theorem class_inter_def {A : Class} : has_inter.inter A = (fun b => A ≠ ↑s0 ∧
  ∀ c : set, (c ∈ A → b ∈ c)) := rfl
theorem set_inter_is_set {s : set} : ((has_inter.inter s.to_Class).is_set) := by
  unfold Class.is_set; by_cases h : s = s0;
  · use s0; unfold has_inter.inter Class.to_has_inter id;
    rw [h]; simp only [ne_eq, not_true_eq_false, false_and];
    rw [←extensionality_belong]; intro a;
    rw [←set_belong_set_to_class, proof_in_Class]; exact empty_false;
  unfold has_inter.inter Class.to_has_inter id;
  have h1 := nonempty_iff_has_element.1 h; rcases h1 with ⟨y, h1⟩;
  use (make_separation y (fun b => s.to_Class ≠ ↑s0 ∧
     ∀ (c : set), c ∈ s.to_Class → b ∈ c));
     rw [←extensionality_belong]; intro a;
  rw [←set_belong_set_to_class];
  have s2 := axiom_of_separation y (fun b => s.to_Class ≠ ↑s0 ∧
     ∀ (c : set), c ∈ s.to_Class → b ∈ c) a;
  rw [s2]; simp only [ne_eq, intersection_def, and_iff_right_iff_imp];
  rw [proof_in_Class]; intro ha;
  exact ha.2 y h1;
noncomputable instance set.to_has_inter : has_inter set :=
⟨ fun s => (has_inter.inter s.to_Class).to_set set_inter_is_set, by
  intro s; simp only [ne_eq]; constructor;
  · intro h; have h : s = s0;
    · rw [←extensionality_belong]; intro a;
      rw [set_belong_to_class, h, ←set_belong_set_to_class];
    rw [h]; unfold has_inter.inter Class.to_has_inter id;
    rw [Class_to_set_to_Class_has_belong, ←extensionality_belong];
    intro a; simp only [ne_eq, not_true_eq_false, false_and];
    rw [proof_in_Class, ←set_belong_set_to_class];
    simp [empty_false];
  · intro h b; unfold has_inter.inter Class.to_has_inter id;
    rw [Class_to_set_ext, proof_in_Class]; simp only [ne_eq];
    constructor <;> intro h1;
    · exact h1.2;
    · use h; intro c; rw [←set_belong_set_to_class]; use h1 c;
⟩
theorem set_inter_def {a : set} : ∀ b : set, b ∈ has_inter.inter a ↔ a ≠ ↑s0 ∧
  ∀ c : set, (c ∈ a → b ∈ c) := by
  intro b; unfold has_inter.inter set.to_has_inter id;
  conv => lhs; rhs; simp; lhs; rw [class_inter_def];
  rw [Class_to_set_ext, proof_in_Class];
  conv => lhs; rhs; ext; lhs; rw [←set_belong_set_to_class];
  simp only [ne_eq, and_congr_left_iff];
  intro h; rw [iff_not_comm]; simp only [not_not];
  constructor <;> intro h1; · rw [h1];
  rw [←extensionality_belong]; intro b;
  rw [set_belong_set_to_class, h1, ←set_belong_set_to_class];

def make_inter_reloaded
  {α : Type u} [has_belong α] [has_inter α] (a : α)
  : α :=
has_inter.inter a

notation "∩(" a ")" => make_inter_reloaded a
notation "{" y " // " x " s∈ " a "}" => (make_replacement a (fun x _y => _y = y))

theorem replacement_notation_def {a y : set} {f : set → set} :
  y ∈ {f x // x s∈ a} ↔ ∃ x s∈ a, y = f x := by
  rw [axiom_of_replacement]; simp;

theorem restrict_intersection [has_belong α] [has_intersection α Class]
  [has_function α] [has_belong β] [has_belong γ] [has_intersection β γ]
  [has_intersection α α]
  {f : α} {a : β} {b : γ} : f Γ (a ∩ b) = (f Γ a) ∩ (f Γ b) := by
  rw [←extensionality_belong]; intro x; simp only [intersection_def];
  rw [belong_restrict, belong_restrict, belong_restrict];
  simp; aesop;
theorem image_intersection [has_belong α] [has_intersection α Class]
  [has_function α] [has_belong β] [has_belong γ] [has_intersection β γ]
  [has_intersection α α]
  {f : α} {a : β} {b : γ} (h0 : Un(f⁻¹)) : f[a ∩ b] = f[a] ∩ f[b] := by
  rw [←extensionality_belong]; intro x; simp only [intersection_def];
  simp only [has_function.proof_range, belong_restrict, intersection_def,
    ordered_pair_eq_iff, exists_and_left, ↓existsAndEq, and_true, exists_eq_right'];
  constructor; · intro h; aesop;
  intro ⟨⟨y, h1, h2⟩, z, h3, h4⟩; rw [←pair_in_inverse] at h1 h3;
  have h5 := h0 _ _ _ ⟨h1, h3⟩; subst y; use z; rw [pair_in_inverse] at h1;
  use h1;

theorem range_eq_S {f a : set} (h : Un(f)) (h1 : a ∈ D(f)) :
  W(f) = W(f Γ (D(f) - s{a})) ∪ s{f[[a]]} := by
  rw [←extensionality_belong]; intro x;
  simp only [has_function.proof_range, binary_union_def, pair_in_restrict,
    set_sub_is_sub, has_function.proof_domain, element_in_one_element_set];
  constructor;
  · intro ⟨y, h2⟩; by_cases h3 : y = a;
    · subst y; right; symm; exact value_func h h2;
    left; use y; use h2; use ⟨x, h2⟩;
  intro h3; cases h3 with
  | inl h3 => rcases h3 with ⟨y, h3, _⟩; exact ⟨y, h3⟩;
  | inr h3 => use a; subst x; exact value_func2 h h1;
theorem range_nin_S {f a : set} (h : Un₂(f)) (h1 : a ∈ D(f)) :
  f[[a]] ∉ W(f Γ (D(f) - s{a})) := by
  intro h2; simp only [has_function.proof_range, pair_in_restrict, set_sub_is_sub,
    has_function.proof_domain, element_in_one_element_set] at h2;
  rcases h2 with ⟨x, h2, ⟨y, h3⟩, h4⟩; have h5 := value_func2 h.1 h1;
  apply h4; rw [←pair_in_inverse] at h2 h5; exact h.2 _ _ _ ⟨h2, h5⟩;
theorem union_sub {a b : set} (h : b ∉ a) : a ∪ s{b} - s{b} = a := by
  rw [←extensionality_belong]; intro x; simp only [set_sub_is_sub, binary_union_def,
    element_in_one_element_set]; rw [or_and_right];
  simp only [and_not_self, or_false, and_iff_left_iff_imp];
  intro h1 h2; subst x; contradiction;

def to_func (f : set → set) : Class :=
  fun c => ∃ x, c = s⟨x, f x⟩
theorem lambda_is_function {f : set → set} : Fnc(to_func f) := by
  constructor;
  · intro c; unfold to_func; rw [proof_in_Class]; simp only [forall_exists_index];
    intro x h; rw [h]; simp;
  intro a b c ⟨ha, hb⟩; unfold to_func at *;
  rw [proof_in_Class] at *; simp at *; aesop;
theorem to_func_eq_value {f : set → set} : (to_func f)[[x]] = f x := by
  apply value_func; · exact lambda_is_function.2;
  unfold to_func; rw [proof_in_Class]; simp;
open Classical in
noncomputable def func_to [has_belong α] [has_intersection α Class]
  [has_function α] (f : α) : set → set :=
  fun x => if h : x ∈ D(f) then
    Classical.choose ((has_function.proof_domain x).1 h)
    else s0
theorem func_to_eq_value [has_belong α] [has_intersection α Class]
  [has_value α] {f : α} (hf : Un(f)) (x : set) (h : x ∈ D(f)) :
  func_to f x = f[[x]] := by
  unfold func_to; simp only [h, ↓reduceDIte];
  have h1 := Classical.choose_spec ((has_function.proof_domain x).1 h);
  have h2 := value_func hf h1; symm; assumption;

theorem E_foundational [has_belong α] [has_intersection α Class]
  {A : α} : is_foundational E A := by
  intro x ⟨h1, h2⟩;
  rcases axiom_of_regularity h2 with ⟨y, h3, h4⟩;
  use y; use h3; rw [E_first];
  rw [←extensionality_belong];
  simp only [intersection_def, ←set_belong_set_to_class];
  conv => ext; rw [And.comm, ←intersection_def];
  rwa [extensionality_belong];
theorem E_well_founded {A : Class} : is_well_founded E A := by
  use E_foundational;
  intro x h; rw [E_first]; rw [intersection_right_set];
  exact ⟨_, rfl⟩
theorem foundational_restrict {A : Class} {a : set} (h : is_foundational A a) :
  is_foundational ((a × a) ∩ A) a := by
  intro x hx; rcases h x hx with ⟨y, h1, h2⟩;
  use y; use h1;
  rw [←h2, ←extensionality_belong]; intro b;
  simp only [intersection_def, and_congr_right_iff]; intro hb;
  rw [has_function.proof_range, has_function.proof_range];
  conv =>
    lhs; rhs; ext; rw [pair_in_restrict]; lhs;
    rw [pair_in_inverse, intersection_def, pair_in_product];
  conv => rhs; rhs; ext; rw [pair_in_restrict, pair_in_inverse];
  simp only [element_in_one_element_set, exists_eq_right, and_iff_right_iff_imp];
  intro; use hx.1 _ hb; use hx.1 y h1;
theorem well_order_restrict {A : Class} {a : set} (h : is_well_order A a) :
  is_well_order ((a × a) ∩ A) a := by
  use (foundational_restrict h.1);
  intro x hx y hy; simp only [intersection_def, pair_in_product];
  have h2 := h.2 x hx y hy; simp only at h2;
  simp only [hx, hy, and_self, true_and]; use h2;

theorem well_found_eqv [has_belong β] [has_intersection β Class] [has_function β]
  [has_intersection set β] {R : β} {a x : set} :
  (a ∩ R⁻¹[s{x}] = s0) ↔ ∀ b s∈ a, ¬(R& b x) := by
  constructor <;> intro h;
  · intro b hb hb2; rw [←@empty_false b, ←h]; simp only [intersection_def]; use hb;
    rw [has_function.proof_range]; use x;
    simp only [pair_in_restrict, element_in_one_element_set, and_true,
      pair_in_inverse]; assumption;
  rw [←extensionality_belong]; intro b;
  simp only [intersection_def, empty_false, iff_false, not_and];
  intro hb hb2; have h := h b hb; apply h;
  rw [has_function.proof_range] at hb2; simp only [pair_in_restrict, element_in_one_element_set,
    exists_eq_right, pair_in_inverse] at hb2; assumption;
theorem well_found_eqv_class [has_belong β] [has_intersection β Class] [has_function β]
  [has_intersection Class β] {R : β} {A : Class} {x : set} :
  (A ∩ R⁻¹[s{x}] = s0) ↔ ∀ b s∈ A, ¬(R& b x) := by
  constructor <;> intro h;
  · intro b hb hb2; rw [←@empty_false b, set_belong_set_to_class, ←h];
    simp only [intersection_def]; use hb;
    rw [has_function.proof_range]; use x;
    simp only [pair_in_restrict, element_in_one_element_set, and_true,
      pair_in_inverse]; assumption;
  rw [←extensionality_belong]; intro b;
  simp only [intersection_def, ←set_belong_set_to_class, empty_false, iff_false, not_and];
  intro hb hb2; have h := h b hb; apply h;
  rw [has_function.proof_range] at hb2; simp only [pair_in_restrict, element_in_one_element_set,
    exists_eq_right, pair_in_inverse] at hb2; assumption;
theorem well_order_minimal [has_belong α] [has_intersection α Class] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β]
  {A : α} {R : β} (h : is_well_order R A) :
  (∀ a : set, a s⊆ A ∧ a ≠ s0 → ∃! x, x ∈ a ∧ a ∩ (R⁻¹[s{x}]) = s0) := by
  intro a ⟨h1, h2⟩; rcases h.1 a ⟨h1, h2⟩ with ⟨x, hx1, hx2⟩; use x;
  use ⟨hx1, hx2⟩; intro y; simp only [and_imp]; intro hy1 hy2;
  rw [well_found_eqv] at hx2 hy2;
  have hx3 := hx2 y hy1; have hy3 := hy2 x hx1; simp at hx3 hy3;
  cases h.2 y (h1 _ hy1) x (h1 _ hx1) with
  | inl => contradiction;
  | inr h => cases h with
    | inl => assumption;
    | inr => contradiction;

theorem foundational_belong_to_3 [has_belong α] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β]
  {A : α} {R : β} (h : is_foundational R A) :
  ∀ x s∈ A, ∀ y s∈ A, ∀ z s∈ A, R& x y → R& y z → R& z x → False := by
  intro x hx y hy z hy h1 h2 h3;
  have hx1 : s{x, y} ∪ s{z} ≠ s0;
  · rw [nonempty_iff_has_element]; use z; simp;
  have hx2 : s{x, y} ∪ s{z} s⊆ A;
  · intro a; simp only [binary_union_def, axiom_of_pair, element_in_one_element_set];
    intro ha; cases' ha with ha ha; cases' ha with ha ha;
    all_goals subst a; assumption;
  have hx3 := h _ ⟨hx2, hx1⟩; simp only [binary_union_def, axiom_of_pair,
    element_in_one_element_set, well_found_eqv, exists_or_eq_imp, ↓existsAndEq,
    true_and] at hx3;
  cases hx3 with
  | inl hx3 => cases hx3 with
    | inl hx3 => exact hx3 z (Or.inr rfl) h3;
    | inr hx3 => exact hx3 x (Or.inl (Or.inl rfl)) h1;
  | inr hx3 => exact hx3 y (Or.inl (Or.inr rfl)) h2;
theorem foundational_belong_to_2 [has_belong α] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β]
  {A : α} {R : β} (h : is_foundational R A) :
  ∀ x s∈ A, ∀ y s∈ A, R& x y → R& y x → False := by
  intro x hx y hy h1 h2;
  have hx1 : s{x, y} ≠ s0;
  · rw [nonempty_iff_has_element]; use y; simp;
  have hx2 : s{x, y} s⊆ A;
  · intro a; simp only [axiom_of_pair];
    intro ha; cases' ha with ha ha;
    all_goals subst a; assumption;
  have hx3 := h _ ⟨hx2, hx1⟩; simp only [axiom_of_pair, well_found_eqv,
    exists_or_eq_imp, ↓existsAndEq, true_and] at hx3;
  cases hx3 with
  | inl hx3 => exact hx3 y (Or.inr rfl) h2;
  | inr hx3 => exact hx3 x (Or.inl rfl) h1;
theorem foundational_belong_to_self [has_belong α] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β]
  {A : α} {R : β} (h : is_foundational R A) :
  ∀ x s∈ A, R& x x → False := by
  intro x hx h1;
  have hx1 : s{x} ≠ s0;
  · rw [nonempty_iff_has_element]; use x; simp;
  have hx2 : s{x} s⊆ A;
  · intro a; simp only [element_in_one_element_set];
    intro ha; subst a; assumption;
  have hx3 := h _ ⟨hx2, hx1⟩; simp only [element_in_one_element_set,
    well_found_eqv, forall_eq, exists_eq_left] at hx3; contradiction;

theorem well_order_trans [has_belong α] [has_intersection α Class] [has_belong β]
  [has_intersection β Class] [has_function β] [has_intersection set β]
  {A : α} {R : β} (h : is_well_order R A) :
  ∀ x s∈ A, ∀ y s∈ A, ∀ z s∈ A, R& x y → R& y z → R& x z := by
  intro x hx y hy z hz h1 h2;
  have h3 := h.2 _ hx _ hz; simp only at h3;
  cases h3 with
  | inl => assumption;
  | inr h3 => cases h3 with
    | inl h3 => subst z; exfalso; exact foundational_belong_to_2 h.1 _ hx _ hy h1 h2;
    | inr h3 =>
      exfalso; exact foundational_belong_to_3 h.1 _ hx _ hy _ hz h1 h2 h3;

theorem wfwo_class_minimal [has_belong α] [has_intersection α Class] [has_function α]
  [has_intersection set α] [has_intersection Class α]
  {R : α} {A B : Class} (h : is_well_founded_well_order R A)
  (hb1 : B s⊆ A) (hb2 : B ≠ s0) : ∃ a s∈ B, B ∩ R⁻¹[s{a}] = s0 := by
  rcases nonempty_class_iff_has_element.1 hb2 with ⟨x, hb3⟩;
  have h1 := h.1.2 x (hb1 _ hb3);
  by_cases hb0 : (B ∩ R⁻¹[s{x}]) = s0; · use x;
  have hb : (B ∩ R⁻¹[s{x}]).is_set;
  · apply @subseteq_is_set ((A ∩ R⁻¹[s{x}]).to_set h1);
    intro y; simp only [intersection_def, Class_to_set_ext];
    exact fun ⟨a, b⟩ ↦ ⟨hb1 _ a, b⟩;
  let b := (B ∩ R⁻¹[s{x}]).to_set hb;
  have hb4 : _;
  · apply h.1.1 b; constructor;
    · intro y yb; unfold b at yb;
      simp only [intersection_def, Class_to_set_ext] at yb; exact hb1 _ yb.1;
    intro hb1; rw [←hb1] at hb0; unfold b at hb0; rw [Class_to_set_to_Class] at hb0;
    exact hb0 rfl;
  rcases hb4 with ⟨y, hy1, hy2⟩; use y; unfold b at hy1 hy2;
  rw [Class_to_set_ext, intersection_def] at hy1; use hy1.1;
  rw [←extensionality_belong]; intro a; rw [←set_belong_set_to_class]; rw [←hy2];
  simp only [intersection_def, Class_to_set_ext, and_congr_left_iff, iff_self_and];
  simp only [has_function.proof_range, pair_in_restrict, pair_in_inverse,
    element_in_one_element_set, exists_eq_right];
  simp only [has_function.proof_range, pair_in_restrict,
    pair_in_inverse, element_in_one_element_set, exists_eq_right] at hy1;
  intro ha1 ha2;
  exact well_order_trans h.2 _ (hb1 _ ha2) _ (hb1 _ hy1.1) _ (hb1 _ hb3) ha1 hy1.2;
theorem well_founded_on_set {R : Class} {a : set} :
  (∀ x s∈ a, has_belong.is_set (a.to_Class ∩ (R⁻¹[s{x}]))) := by
  intro x hx; rw [intersection_comm, intersection_right_set];
  exact set_to_Class_is_set;

end zfset
