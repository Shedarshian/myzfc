import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals

namespace zfset

def ord_add_h : Class := fun c => ∃ x, c = s⟨x, succ_set x⟩
theorem ord_add_h_value (x : set) : ord_add_h[[x]] = succ_set x := by
  apply value_func;
  · intro u v w ⟨h1, h2⟩; unfold ord_add_h at h1 h2;
    rw [proof_in_Class] at h1 h2; simp at h1 h2; aesop;
  unfold ord_add_h; rw [proof_in_Class]; simp;
def ord_add (α : set) : Class := trans_rec_func ord_add_h α

theorem ord_add_set1 (α) : (ord_add α)[[s0]] = α := trans_func_rec1
theorem ord_add_set2 (α β) : (ord_add α)[[(succ β).val]] =
  succ_set ((ord_add α)[[β.val]]) := by
  unfold ord_add; rw [trans_func_rec2, ord_add_h_value];
theorem ord_add_set3 (α : set) (β : ordinal) : β ∈ K2 → (ord_add α)[[β.val]] =
  ∪({(ord_add α)[[γ.val]] // γ o∈ β}) := trans_func_rec3

theorem ord_add_is_ord (α β : ordinal) : Ord((ord_add α.val)[[β.val]]) := by
  apply ordinal.induction β; intro β hg;
  cases k12 β with
  | inl h =>
    cases h with
    | inl h1 => rw [h1, o0_eq_s0, ord_add_set1]; exact α.prop;
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩;
      rw [h1, ord_add_set2]; rw [h1] at hg;
      have hg := hg δ ord_lt_succ;
      exact (succ ⟨ord_add α.val[[δ.val]], hg⟩).prop;
  | inr h =>
    rw [ord_add_set3]; swap; · assumption;
    apply ord_class_union_ordinal;
    intro x hx; rw [ordinal_replacement_axiom] at hx;
    · rcases hx with ⟨y, h1, h2⟩; rw [h2];
      have hy := ord_element_ord' β.val y.val β.prop h1;
      have hc : y < β; · exact h1;
      exact hg _ hc;
    intro u v w ⟨h1, h2⟩; aesop;

noncomputable instance ordinal.add : Add ordinal :=
⟨ fun α β => ⟨(ord_add α.val)[[β.val]], ord_add_is_ord α β⟩ ⟩

@[simp] theorem ord_add1 {α} : α + o0 = α :=
  Subtype.ext (ord_add_set1 α.val)
@[simp] theorem ord_add2 {α β} : α + succ β = succ (α + β) :=
  Subtype.ext (ord_add_set2 α.val β)
theorem ord_add3 {α β : ordinal} : β ∈ K2 → α + β = ⋃(γ oo∈ β, α + γ) :=
  by
    intro h; apply Subtype.ext;
    erw [←ordinal_union_axiom, ←ord_add_set3 _ _ h]; rfl;

@[simp] theorem ord_zero_add {α} : o0 + α = α := by
  apply ordinal.induction α; intro α hg;
  cases k12 α with
  | inl h =>
    cases h with
    | inl h => rw [h]; simp;
    | inr h =>
      rcases h with ⟨β, h⟩; rw [h, ord_add2];
      rw [h] at hg; have hg := hg β ord_lt_succ;
      rw [hg];
  | inr h =>
    rw [ord_add3 h, ordinal_union_replace hg];
    apply Subtype.ext; rw [←ordinal_union_axiom];
    erw [ordinal_replacement_id]; exact ord_k2_union_eq_self h;
theorem ord_lt_left_add {α β γ : ordinal} : α < β → γ + α < γ + β := by
  apply ordinal.induction β; intro β h ha;
  cases k12 β with
  | inl hb => cases hb with
    | inl => subst β ; exfalso; exact empty_false.1 ha;
    | inr hb =>
      rcases hb with ⟨β', hb⟩; subst β;
      rw [ord_lt_succ_iff, ord_le] at ha;
      cases ha with
      | inl ha =>
        have h := h β' ord_lt_succ ha;
        apply ord_lt_trans h; simp only [ord_add2]; exact ord_lt_succ;
      | inr => subst α; simp only [ord_add2]; exact ord_lt_succ;
  | inr hb =>
    rw [ord_add3 hb]; apply ord_lt_le_trans; · exact ord_lt_succ;
    rw [←ord_add2]; apply ord_union_le_sup; exact ord_k2_succ_in hb ha;
theorem ord_lt_add_left_elim {α β γ : ordinal} : α < β ↔ γ + α < γ + β :=
  Iff.intro ord_lt_left_add (by
    intro h;
    cases @ord_total α β with
    | inl => assumption;
    | inr h1 => cases h1 with
      | inl => subst α; exfalso; exact belong_to_self h;
      | inr h1 =>
        have h2 := @ord_lt_left_add _ _ γ h1;
        exfalso; exact belong_to_2 h h2;
  )
theorem ord_add_left_elim {α β γ : ordinal} : γ + α = γ + β ↔ α = β := by
  constructor <;> intro h; swap; · rw [h];
  cases' @ord_total α β with h1 h1; swap;
  cases' h1 with h1 h1; · assumption;
  all_goals
    have h2 := @ord_lt_left_add _ _ γ h1; rw [h] at h2;
    exfalso; exact belong_to_self h2;
theorem ord_le_left_add {α β γ : ordinal} : α ≤ β → γ + α ≤ γ + β := by
  intro h;
  cases ord_le.1 h with
  | inr => subst β; rfl;
  | inl h2 => apply ord_le.2; left; exact ord_lt_left_add h2;

theorem ordinal_union_le_union {α β : ordinal} {f g : ordinal → ordinal} :
  (∀ δ o∈ α, ∃ ε o∈ β, f δ ≤ g ε) → ⋃(γ oo∈ α, f γ) ≤ ⋃(γ oo∈ β, g γ) := by
  intro hz x h; erw [set_ord_belong] at h;
  erw [←ordinal_union_axiom, has_union.proof_union] at h;
  have h0 : ∀ (f : ordinal → ordinal) (u : ordinal) (v w : set),
    v = (f u).val ∧ w = (f u).val → v = w;
  · simp;
  rcases h with ⟨c, h1, h2⟩; rw [ordinal_replacement_axiom _ _ (h0 f)] at h2;
  rcases h2 with ⟨d, h2, h3⟩; rcases hz d h2 with ⟨e, h4, h5⟩;
  subst c; have h5 := h5 _ h1;
  have o := ord_element_ord' (f d) x (f d).prop h1;
  apply @ord_lt_le_trans ⟨x, o⟩ _ _ h5;
  apply ord_union_le_sup _ h4;

theorem ord_le_right_add {α β γ : ordinal} : α ≤ β → α + γ ≤ β + γ := by
  intro h; apply ordinal.induction γ; intro γ h0;
  cases k12 γ with
  | inl h => cases h with
    | inl h => subst γ; simp only [ord_add1]; assumption;
    | inr h =>
      rcases h with ⟨δ, h⟩; subst γ; simp only [ord_add2];
      apply ord_succ_le_succ; exact h0 δ ord_lt_succ;
  | inr h =>
    rw [ord_add3 h, ord_add3 h]; apply ordinal_union_le_union;
    intro δ hd; use δ; use hd; exact h0 δ hd;
theorem ord_lt_right_add_elim {α β γ : ordinal} : α + γ < β + γ → α < β := by
  intro h; cases @ord_total α β with
  | inl => assumption;
  | inr h1 =>
    symm at h1; conv at h1 => rhs; rw [Eq.comm];
    rw [←ord_le] at h1; have h1 := @ord_le_right_add _ _ γ h1; exfalso;
    exact belong_to_self (ord_le_lt_trans h1 h)

theorem ord_sub {α β : ordinal} : α ≤ β → ∃!γ : ordinal, α + γ = β := by
  intro h; have h1 := @ord_le_right_add _ α β ord_ge_0; rw [ord_zero_add] at h1;
  have he := @minimal_ordinal (fun γ => β ≤ α + γ) ⟨β, h1⟩;
  rcases he with ⟨γ, h2, h3⟩;
  suffices hm : α + γ = β;
  · use γ; simp only; constructor;
    · assumption;
    · intro y hy; rwa [←hm, ord_add_left_elim] at hy;
  cases k12 γ with
  | inl h0 => cases h0 with
    | inl h0 => subst γ; simp only [ord_add1] at *; exact subseteq_antisymm h h2;
    | inr h0 =>
      rcases h0 with ⟨δ, h0⟩; subst γ; rw [ord_le] at h2;
      cases h2 with
      | inr => symm; assumption;
      | inl h2 =>
        rw [ord_add2, ord_lt_succ_iff] at h2; exfalso;
        have h3 := ord_lt_le_trans ord_lt_succ (h3 _ h2);
        exact belong_to_self h3;
  | inr h0 =>
    apply subseteq_antisymm; swap; · assumption;
    rw [ord_add3 h0]; intro x hx;
    have ho := ord_element_ord _ _ hx;
    unfold ordinal_function_union at hx; simp only at hx;
    erw [set_ord_belong, has_union.proof_union] at hx;
    have h : ∀ (f : ordinal → ordinal), ∀ (u v w : ordinal),
      v = f u ∧ w = f u → v = w;
    · simp only [and_imp, forall_eq_apply_imp_iff, imp_self, implies_true];
    conv at hx => rhs; ext; rhs; erw [ordinal_replacement_axiom2 _ _ (h _)];
    simp only [↓existsAndEq, and_self, and_true] at hx;
    have h3 := fun γ_1 => mt (h3 γ_1);
    conv at h3 => rhs; rw [ord_nle, ord_nle];
    rcases hx with ⟨δ, hx1, hx2⟩;
    have h3 := h3 _ hx2; exact @ord_lt_trans ⟨x, ho⟩ _ _ hx1 h3;

theorem ord_add_k2_in_k2 {α β : ordinal} : β ∈ K2 → α + β ∈ K2 := by
  intro h; have h' := h; erw [ord_in_k2] at h; erw [ord_in_k2];
  constructor <;> intro hn;
  · have h1 := @ord_le_right_add _ α β ord_ge_0; rw [ord_zero_add] at h1;
    conv at h => lhs; rhs; rw [Eq.comm];
    have hb := ord_lt.2 ⟨@ord_ge_0 β, h.1⟩;
    have ht := ord_lt_le_trans hb h1; rw [hn] at ht; exact belong_to_self ht;
  rcases hn with ⟨γ, hn⟩; rw [ord_add3 h'] at hn;
  have h1 := @ord_lt_succ γ; rw [←hn] at h1;
  rw [ordinal_union_lt] at h1;
  rcases h1 with ⟨c, h1, h2⟩; have hc := ord_k2_succ_in h' h1;
  have h4 : succ γ < ⋃(γ oo∈ β, α + γ);
  · rw [ordinal_union_lt]; use succ c; use hc; simp only [ord_add2];
    apply ord_succ_lt_succ h2;
  rw [hn] at h4; exact belong_to_self h4;

theorem ord_add_assoc {α β γ : ordinal} : (α + β) + γ = α + (β + γ) := by
  apply ordinal.induction γ; intro γ h0;
  cases k12 γ with
  | inl h => cases h with
    | inl h => subst γ; simp;
    | inr h =>
      rcases h; subst γ; simp only [ord_add2]; congr 1;
      apply h0; exact ord_lt_succ;
  | inr h =>
    rw [ord_add3 h]; have h2 := @ord_add_k2_in_k2 β γ h;
    rw [ord_add3 h2];
    apply subseteq_antisymm <;> apply ordinal_union_le_union <;> intro δ h3;
    · use β + δ; use ord_lt_left_add h3; rw [h0 δ h3];
    cases @ord_total δ β with
    | inl h4 =>
      use o0; constructor;
      · rw [ord_in_k2] at h; have h5 := @ord_ge_0 γ;
        rw [ord_le] at h5; cases h5 with
        | inl => assumption;
        | inr h5 => symm at h5; exfalso; exact h.1 h5;
      simp only [ord_add1]; apply ord_lt_le; exact ord_lt_left_add h4;
    | inr h4 =>
      symm at h4; conv at h4 => rhs; rw [Eq.comm];
      rw [←ord_le] at h4;
      rcases ord_sub h4 with ⟨ε, h4, h5⟩; use ε;
      suffices h6 : ε < γ; · use h6; rw [h0 _ h6]; rw [←h4];
      rw [←h4] at h3; exact ord_lt_add_left_elim.2 h3;

def ord_mul_h (α : ordinal) : Class := fun c =>
  ∃ x : ordinal, c = s⟨x.val, (x + α).val⟩
theorem ord_mul_h_value (α x : ordinal) : (ord_mul_h α)[[x.val]] = (x + α).val := by
  apply value_func;
  · intro u v w ⟨h1, h2⟩; unfold ord_mul_h at h1 h2;
    rw [proof_in_Class] at h1 h2; simp only [ordered_pair_eq_iff] at h1 h2;
    rcases h1; rcases h2;
    rename_i h w_2 h_1;
    simp_all only;
    obtain ⟨left, right⟩ := h;
    obtain ⟨left_1, right_1⟩ := h_1;
    subst right left_1 right_1;
    have h := Subtype.ext left; aesop;
  unfold ord_mul_h; rw [proof_in_Class]; simp only [ordered_pair_eq_iff]; use x;
def ord_mul (α : ordinal) : Class := trans_rec_func (ord_mul_h α) s0

theorem ord_mul_set1 (α) : (ord_mul α)[[s0]] = s0 := trans_func_rec1
theorem ord_mul_set3 (α) (β : ordinal) : β ∈ K2 → (ord_mul α)[[β.val]] =
  ∪({(ord_mul α)[[γ.val]] // γ o∈ β}) := trans_func_rec3

theorem ord_mul_is_ord (α β : ordinal) : Ord((ord_mul α)[[β.val]]) := by
  apply ordinal.induction β; intro β hg;
  cases k12 β with
  | inl h =>
    cases h with
    | inl h1 => rw [h1, o0_eq_s0, ord_mul_set1]; exact o0.prop;
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst β;
      have ho := hg _ ord_lt_succ;
      unfold ord_mul at *; rw [trans_func_rec2];
      have hz : trans_rec_func (ord_mul_h α) s0[[δ.val]] =
        (⟨trans_rec_func (ord_mul_h α) s0[[δ.val]], ho⟩ : ordinal).val;
        · rfl;
      rw [hz, ord_mul_h_value];
      exact ord_add_is_ord ⟨(ord_mul α)[[δ.val]], ho⟩ α;
  | inr h =>
    rw [ord_mul_set3]; swap; · assumption;
    apply ord_class_union_ordinal;
    intro x hx; rw [ordinal_replacement_axiom] at hx;
    · rcases hx with ⟨y, h1, h2⟩; rw [h2];
      have hy := ord_element_ord' β.val y.val β.prop h1;
      have hc : y < β; · exact h1;
      exact hg _ hc;
    intro u v w ⟨h1, h2⟩; aesop;

noncomputable instance ordinal.mul : Mul ordinal :=
⟨ fun α β => ⟨(ord_mul α)[[β.val]], ord_mul_is_ord α β⟩ ⟩

@[simp] theorem ord_mul1 {α} : α * o0 = o0 :=
  Subtype.ext (ord_mul_set1 α)
@[simp] theorem ord_mul2 {α β} : α * succ β = α * β + α := by
  apply Subtype.ext; unfold_projs; simp only; unfold ord_mul;
  have h := @trans_func_rec2 (ord_mul_h α) s0 β; unfold_projs at h;
  have h2 := ord_mul_h_value α (⟨value (trans_rec_func (ord_mul_h α) s0) β.val,
    ord_mul_is_ord _ _⟩); unfold_projs at h2; simp only at h2;
  erw [h, h2];
theorem ord_mul3 {α β : ordinal} : β ∈ K2 → α * β = ⋃(γ oo∈ β, α * γ) :=
  by
    intro h; apply Subtype.ext;
    erw [←ordinal_union_axiom, ←ord_mul_set3 _ _ h]; rfl;

@[simp] theorem ord_zero_mul {α : ordinal} : o0 * α = o0 := by
  apply ordinal.induction α; intro α h;
  cases k12 α with
  | inl h1 => cases h1 with
    | inl => subst α; simp;
    | inr h1 =>
      rcases h1 with ⟨β, h1⟩; subst α; have h1 := h _ ord_lt_succ;
      rw [ord_mul2, h1]; simp;
  | inr h1 =>
    rw [ord_mul3 h1, ordinal_union_replace h];
    rw [←extensionality_belong]; intro a; erw [empty_false]; simp only [iff_false];
    intro h2; rw [ordinal_union_set] at h2; rcases h2 with ⟨_, _, h2⟩
    exact empty_false.1 h2;
@[simp] theorem ord_one_mul {α : ordinal} : (succ o0) * α = α := by
  apply ordinal.induction α; intro α h;
  cases k12 α with
  | inl h1 => cases h1 with
    | inl => subst α; simp;
    | inr h1 =>
      rcases h1 with ⟨β, h1⟩; subst α; have h1 := h _ ord_lt_succ;
      rw [ord_mul2, h1]; simp;
  | inr h1 =>
    rw [ord_mul3 h1, ordinal_union_replace h];
    rw [←extensionality_belong]; intro a;
    have : ⋃(γ oo∈ α, γ) = α;
    · apply Subtype.ext; rw [←ordinal_union_axiom];
      erw [ordinal_replacement_id];
      rw [ord_k2_union_eq_self h1];
    rw [this]

theorem ord_lt_left_mul {α β γ : ordinal} : o0 < γ ∧ α < β ↔ γ * α < γ * β := by
  have ht : ∀ {α β : ordinal}, o0 < γ ∧ α < β → γ * α < γ * β;
  · intro α β h0; rcases h0 with ⟨h0, h1⟩;
    have h1 := ord_sub (ord_succ_belong_le h1);
    rcases h1 with ⟨δ, h1, h2⟩; subst β; apply ordinal.induction δ; intro β h3;
    cases k12 β with
    | inl h1 => cases h1 with
      | inl =>
        subst β; simp only [ord_add1, ord_mul2, gt_iff_lt];
        have h4 := @ord_lt_left_add _ _ (γ * α) h0; simp only [ord_add1] at h4; exact h4;
      | inr h1 =>
        rcases h1 with ⟨δ, h1⟩; subst β; simp only [ord_add2, ord_mul2, gt_iff_lt];
        apply ord_lt_trans;
        · exact h3 δ ord_lt_succ;
        have h4 := @ord_lt_left_add _ _ (γ * (succ α + δ)) h0;
        simp only [ord_add1] at h4; exact h4;
    | inr h1 =>
      have h4 := @ord_add_k2_in_k2 (succ α) β h1;
      rw [ord_mul3 h4]; apply @ord_lt_trans _ (γ * (succ α));
      · simp only [ord_mul2]; have h4 := @ord_lt_left_add _ _ (γ * α) h0;
        simp only [ord_add1] at h4; exact h4;
      rw [ordinal_union_lt]; use succ α + succ o0; constructor;
      · apply ord_lt_left_add; exact ord_k2_succ_in h1 (ord_k2_gt_0 h1);
      simp only [ord_mul2, ord_add2, ord_add1];
      have h5 := @ord_lt_left_add _ _ (γ * α + γ) h0;
      simp only [ord_add1] at h5; exact h5;
  use ht; intro h0; have h1 := @ord_ge_0 γ; rw [ord_le] at h1; cases h1 with
  | inr => subst γ; simp at h0;
  | inl h1 => use h1; cases @ord_total α β with
    | inl => assumption;
    | inr h2 => cases h2 with
      | inl => subst α; exfalso; exact belong_to_self h0;
      | inr h2 => have h3 := ht ⟨h1, h2⟩; exfalso; exact belong_to_2 h0 h3;
theorem ord_lt_mul_left_elim {α β γ : ordinal} : o0 < γ → γ * α = γ * β → α = β := by
  intro h1 h2;
  cases' @ord_total α β with h h; swap;
  cases' h with h h; · assumption;
  all_goals
    have h := ord_lt_left_mul.1 ⟨h1, h⟩; rw [h2] at h;
    exfalso; exact belong_to_self h;
theorem ord_le_left_mul {α β γ : ordinal} : α ≤ β → γ * α ≤ γ * β := by
  intro h;
  cases ord_le.1 (@ord_ge_0 γ) with
  | inr => subst γ; simp;
  | inl h1 => cases ord_le.1 h with
    | inr => subst β; rfl;
    | inl h2 => apply ord_le.2; left; exact ord_lt_left_mul.1 ⟨h1, h2⟩;

theorem ord_le_right_mul {α β γ : ordinal} : α ≤ β → α * γ ≤ β * γ := by
  intro h; apply ordinal.induction γ; intro γ h1;
  cases k12 γ with
  | inl h0 => cases h0 with
    | inl => subst γ; simp;
    | inr h0 =>
      rcases h0 with ⟨δ, h0⟩; subst γ; simp only [ord_mul2];
      have h2 := h1 _ ord_lt_succ;
      apply ord_le_trans; · exact ord_le_right_add h2;
      cases ord_le.1 h with
      | inr => subst α; rfl;
      | inl => apply ord_lt_le; apply ord_lt_left_add; assumption;
  | inr h0 =>
    rw [ord_mul3 h0, ord_mul3 h0];
    apply ord_union_sup_le; intro δ h2;
    apply ord_le_trans; · use h1 _ h2;
    apply ord_union_le_sup; assumption;
theorem ord_mul_eq_0 {α β : ordinal} : α * β = o0 ↔ α = o0 ∨ β = o0 := by
  constructor; swap;
  · intro h; apply Or.elim h <;> intro h <;> rw [h] <;> simp;
  intro h; by_contra h1; push Not at h1; rcases h1 with ⟨h1, h2⟩;
  have h1 := ord_ne_0_gt h1;
  have h2 := ord_succ_belong_le (ord_ne_0_gt h2);
  have h4 := @ord_le_left_mul _ _ α h2;
  simp only [ord_mul2, ord_mul1, ord_zero_add] at h4;
  have h3 := ord_lt_le_trans h1 h4; rw [h] at h3; exact belong_to_self h3;
theorem ord_mul_gt_0 {α β : ordinal} : o0 < α * β ↔ o0 < α ∧ o0 < β := by
  rw [←ord_ne_0_gt_iff, not_iff_comm, not_and_or];
  rw [←ord_ne_0_gt_iff, ←ord_ne_0_gt_iff]; simp only [not_not];
  exact Iff.symm ord_mul_eq_0;
theorem ord_mul_k2_in_k2 {α β : ordinal} : α ≠ o0 → β ∈ K2 → α * β ∈ K2 := by
  intro h0 h; have h' := h; erw [ord_in_k2] at h; erw [ord_in_k2];
  constructor <;> intro hn;
  · rw [ord_mul_eq_0] at hn; have hn2 := And.intro h0 h.1;
    have hn := not_not.2 hn; apply hn; push Not; exact hn2;
  rcases hn with ⟨γ, hn⟩; rw [ord_mul3 h'] at hn;
  have h1 := @ord_lt_succ γ; rw [←hn] at h1;
  rw [ordinal_union_lt] at h1; rcases h1 with ⟨δ, h2, h3⟩;
  have h4 := calc
    succ γ  < succ (α * δ)      := by exact ord_succ_lt_succ h3;
         _  = α * δ + succ o0   := by simp;
         _  ≤ α * δ + α         := by
                                    apply ord_le_left_add;
                                    apply ord_succ_belong_le;
                                    apply ord_ne_0_gt; exact h0;
         _  = α * succ δ        := by simp;
  have h5 := ord_k2_succ_in h' h2;
  have h6 := @ord_union_le_sup _ (fun n ↦ α * n) _ h5;
  rw [hn] at h6; have h7 := ord_lt_le_trans h4 h6;
  exact belong_to_self h7;

theorem ord_mul_add {α β γ : ordinal} : α * (β + γ) = α * β + α * γ := by
  apply ordinal.induction γ; intro γ h;
  cases k12 γ with
  | inl h1 => cases h1 with
    | inl => subst γ; simp;
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst γ; simp only [ord_add2, ord_mul2];
      rw [h _ ord_lt_succ]; exact ord_add_assoc;
  | inr h1 =>
    cases ord_le.1 (@ord_ge_0 α) with
    | inr h2 => subst α; simp;
    | inl h2 =>
      rw [ord_mul3 (ord_add_k2_in_k2 h1)];
      rw [ord_add3 (ord_mul_k2_in_k2 (ord_ne_0_gt_iff.2 h2) h1)];
      apply ord_le_antisymm <;> apply ord_union_sup_le <;> intro δ h3;
      · cases @ord_total δ β with
        | inl h4 =>
          apply ord_le_trans;
          · apply ord_lt_le; apply ord_lt_left_mul.1 ⟨h2, h4⟩;
          nth_rewrite 1 [←@ord_add1 (α * β)];
          apply ord_union_le_sup; apply ord_k2_gt_0;
          exact ord_mul_k2_in_k2 (ord_ne_0_gt_iff.2 h2) h1;
        | inr h4 =>
          symm at h4; conv at h4 => rhs; rw [Eq.comm];
          rw [←ord_le] at h4;
          rcases ord_sub h4 with ⟨ε, h5, _⟩; subst δ;
          have h3 := ord_lt_add_left_elim.2 h3;
          rw [h _ h3]; apply ord_union_le_sup; exact ord_lt_left_mul.1 ⟨h2, h3⟩;
      rw [ord_mul3 h1] at h3; have h3 := ordinal_union_lt.1 h3;
      rcases h3 with ⟨η, h3, h4⟩; apply ord_le_trans;
      · apply ord_lt_le; exact ord_lt_left_add h4;
      rw [←h _ h3]; apply ord_union_le_sup; exact ord_lt_left_add h3;
theorem ord_mul_assoc {α β γ : ordinal} : α * (β * γ) = (α * β) * γ := by
  apply ordinal.induction γ; intro γ h;
  cases k12 γ with
  | inl h1 => cases h1 with
    | inl => subst γ; simp;
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst γ; simp only [ord_mul2];
      rw [ord_mul_add, h _ ord_lt_succ];
  | inr h1 =>
    cases ord_le.1 (@ord_ge_0 (α * β)) with
    | inr h2 =>
      rw [←h2]; cases ord_mul_eq_0.1 (Eq.symm h2) with
      | inl => subst α; simp;
      | inr => subst β; simp;
    | inl h2 =>
      have h3 := ord_mul_gt_0.1 h2;
      rw [ord_mul3 (ord_mul_k2_in_k2 (ord_ne_0_gt_iff.2 h3.2) h1)];
      rw [@ord_mul3 (α * β) _ h1];
      apply ord_le_antisymm <;> apply ord_union_sup_le <;> intro δ h4;
      · rw [ord_mul3 h1] at h4; have h3 := ordinal_union_lt.1 h4;
        rcases h3 with ⟨η, h4, h5⟩; apply ord_le_trans;
        · apply ord_lt_le; exact ord_lt_left_mul.1 ⟨h3.1, h5⟩;
        rw [h _ h4];
        apply @ord_union_le_sup γ (fun n ↦ α * β * n); exact h4;
      apply ord_le_trans;
      · apply ord_lt_le; exact ord_lt_left_mul.1 ⟨h2, ord_lt_succ⟩;
      have h5 := ord_k2_succ_in h1 h4;
      rw [←h _ h5]; apply ord_union_le_sup;
      exact ord_lt_left_mul.1 ⟨h3.2, h5⟩;

def ord_pow_h (α : ordinal) : Class := fun c =>
  ∃ x : ordinal, c = s⟨x.val, (x * α).val⟩
theorem ord_pow_h_value (α x : ordinal) : (ord_pow_h α)[[x.val]] = (x * α).val := by
  apply value_func;
  · intro u v w ⟨h1, h2⟩; unfold ord_pow_h at h1 h2;
    rw [proof_in_Class] at h1 h2; simp only [ordered_pair_eq_iff] at h1 h2;
    rcases h1; rcases h2;
    rename_i h w_2 h_1;
    simp_all only;
    obtain ⟨left, right⟩ := h;
    obtain ⟨left_1, right_1⟩ := h_1;
    subst right left_1 right_1;
    have h := Subtype.ext left; aesop;
  unfold ord_pow_h; rw [proof_in_Class]; simp only [ordered_pair_eq_iff]; use x;
open Classical in
def ord_pow (α : ordinal) : Class :=
  fun b => if α = o0 then b = s⟨s0, succ_set s0⟩ ∨ ∃ x, b = s⟨x, s0⟩ else
  trans_rec_func (ord_pow_h α) (succ_set s0) b


end zfset
