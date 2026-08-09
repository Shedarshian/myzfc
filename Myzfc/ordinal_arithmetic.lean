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
    intro x hx; rw [mem_ordinal_replacement0] at hx;
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
  rcases h with ⟨c, h1, h2⟩; rw [mem_ordinal_replacement0 _ _ (h0 f)] at h2;
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
    conv at hx => rhs; ext; rhs; erw [mem_ordinal_replacement2 _ _ (h _)];
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
      · rw [←ord_belonged_to, ord_in_k2] at h; have h5 := @ord_ge_0 γ;
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
    intro x hx; rw [mem_ordinal_replacement0] at hx;
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
@[simp] theorem ord_one_mul {α : ordinal} : o1 * α = α := by
  apply ordinal.induction α; intro α h;
  cases k12 α with
  | inl h1 => cases h1 with
    | inl => subst α; simp;
    | inr h1 =>
      rcases h1 with ⟨β, h1⟩; subst α; have h1 := h _ ord_lt_succ;
      rw [ord_mul2, h1]; unfold o1; simp;
  | inr h1 =>
    rw [ord_mul3 h1, ordinal_union_replace h];
    rw [←extensionality_belong]; intro a;
    have : ⋃(γ oo∈ α, γ) = α;
    · apply Subtype.ext; rw [←ordinal_union_axiom];
      erw [ordinal_replacement_id];
      have h0 : α.to_ordset.val = α.val := rfl; rw [h0, ord_k2_union_eq_self h1];
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
      rw [ordinal_union_lt]; use succ α + o1; constructor;
      · apply ord_lt_left_add; exact ord_k2_succ_in h1 (ord_k2_gt_0 h1);
      unfold o1; simp only [ord_mul2, ord_add2, ord_add1];
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
         _  = α * δ + o1        := by unfold o1; simp;
         _  ≤ α * δ + α         := by
                                    apply ord_le_left_add;
                                    apply ord_succ_belong_le;
                                    apply ord_ne_0_gt; exact h0;
         _  = α * succ δ        := by simp;
  have h5 := ord_k2_succ_in h' h2;
  have h6 := @ord_union_le_sup _ (fun n ↦ α * n) _ h5;
  rw [hn] at h6; have h7 := ord_lt_le_trans h4 h6;
  exact belong_to_self h7;

theorem ord_div {α β : ordinal} : β ∈ K2 → γ < α * β → ∃ δ < β, γ < α * δ := by
  intro h h1; rw [ord_mul3 h] at h1; exact ord_lt_union h1;

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
open Classical in def ord_pow (α : ordinal) : Class :=
  fun b => if α = o0 then b = s⟨s0, succ_set s0⟩ ∨ ∃ x, x ≠ s0 ∧ b = s⟨x, s0⟩ else
  trans_rec_func (ord_pow_h α) (succ_set s0) b

theorem ord_pow0_func : Fnc_on (ord_pow o0) V := by
  unfold ord_pow; simp only [↓reduceIte, ne_eq]; constructor; constructor;
  · intro x h; simp only [proof_in_Class] at h; cases h with
    | inl => subst x; simp;
    | inr h => rcases h with ⟨h1, h2, h3⟩; subst x; simp;
  · intro u v w ⟨hv, hw⟩; simp only [proof_in_Class, ordered_pair_eq_iff] at hv hw;
    cases hv with
    | inl hv => rw [hv.1] at hw; simp at hw; aesop;
    | inr hv => rcases hv with ⟨h1, h2, h3⟩; aesop;
  rw [←extensionality_belong]; intro x; simp only [proof_in_Class, set_in_allset_prop,
    has_function.proof_domain, ordered_pair_eq_iff, ↓existsAndEq, true_and, true_iff];
  by_cases x = s0; · subst x; simp only [true_and, not_true_eq_false, false_and, or_false,
    exists_eq];
  · use s0; simp only [and_true]; right; assumption;
theorem ord_pow_set00 : (ord_pow o0)[[s0]] = succ_set s0 := by
  have h0 : s⟨s0, succ_set s0⟩ ∈ ord_pow o0; · unfold ord_pow; simp only [↓reduceIte,
    proof_in_Class, ordered_pair_eq_iff, ↓existsAndEq, true_and, true_or];
  exact value_func ord_pow0_func.1.2 h0;
theorem ord_pow_set01 : a ≠ s0 → (ord_pow o0)[[a]] = s0 := by
  intro h;
  have h0 : s⟨a, s0⟩ ∈ ord_pow o0;
  · unfold ord_pow; simp only [↓reduceIte, ne_eq, proof_in_Class, ordered_pair_eq_iff,
    and_true, exists_eq_right']; right; assumption;
  exact value_func ord_pow0_func.1.2 h0;
theorem ord_pow_setn0 {α} (h : α ≠ o0) : ord_pow α = trans_rec_func (ord_pow_h α) (succ_set s0)
  := by
  rw [←extensionality_belong]; intro x; unfold ord_pow;
  simp only [h, ↓reduceIte, proof_in_Class];
theorem ord_pow_set1 (α) : (trans_rec_func (ord_pow_h α) (succ_set s0))[[s0]] = succ_set s0 :=
  trans_func_rec1
theorem ord_pow_set3 (α) (β : ordinal) : β ∈ K2 →
  (trans_rec_func (ord_pow_h α) (succ_set s0))[[β.val]] =
  ∪({(trans_rec_func (ord_pow_h α) (succ_set s0))[[γ.val]] // γ o∈ β}) := trans_func_rec3

theorem ord_pow_is_ord2 (α β : ordinal) :
  Ord(trans_rec_func (ord_pow_h α) (succ_set s0)[[β.val]]) := by
  apply ordinal.induction β; intro β hg;
  cases k12 β with
  | inl h =>
    cases h with
    | inl h1 => rw [h1, o0_eq_s0, ord_pow_set1]; exact o1.prop;
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst β;
      have ho := hg _ ord_lt_succ;
      rw [trans_func_rec2];
      have hz : trans_rec_func (ord_pow_h α) (succ_set s0)[[δ.val]] =
        (⟨trans_rec_func (ord_pow_h α) (succ_set s0)[[δ.val]], ho⟩ : ordinal).val;
        · rfl;
      rw [hz, ord_pow_h_value];
      exact ord_mul_is_ord _ α;
  | inr h =>
    rw [ord_pow_set3]; swap; · assumption;
    apply ord_class_union_ordinal;
    intro x hx; rw [mem_ordinal_replacement0] at hx;
    · rcases hx with ⟨y, h1, h2⟩; rw [h2];
      have hy := ord_element_ord' β.val y.val β.prop h1;
      have hc : y < β; · exact h1;
      exact hg _ hc;
    intro u v w ⟨h1, h2⟩; aesop;
theorem ord_pow_is_ord (α β : ordinal) : Ord((ord_pow α)[[β.val]]) := by
  by_cases h : α = o0;
  · subst α; by_cases h0 : β = o0; · subst β; rw [o0_eq_s0, ord_pow_set00]; exact o1.prop;
    convert_to Ord(s0); · apply ord_pow_set01; intro h; apply h0; exact Subtype.ext h;
    exact o0.prop;
  rw [ord_pow_setn0 h]; exact ord_pow_is_ord2 _ _;

noncomputable instance ordinal.pow : Pow ordinal ordinal :=
⟨ fun α β => ⟨(ord_pow α)[[β.val]], ord_pow_is_ord α β⟩ ⟩

lemma ord_pow00 : o0 ^ o0 = o1 := Subtype.ext ord_pow_set00
@[simp] theorem ord_pow01 {α} (h : α ≠ o0) : o0 ^ α = o0 :=
  Subtype.ext (ord_pow_set01 fun s ↦ h (Subtype.ext s))
@[simp] theorem ord_pow1 {α} : α ^ o0 = o1 := by
  by_cases h : α = o0; · subst α; exact ord_pow00;
  unfold_projs; apply Subtype.ext; simp only;
  unfold ord_pow; simp only [h, ↓reduceIte]; exact ord_pow_set1 α;
theorem ord_pow2 {α β : ordinal} : α ^ succ β = α ^ β * α := by
  by_cases h : α = o0;
  · subst α; simp only [ord_mul1];
    exact Subtype.ext (ord_pow_set01 fun s ↦ peano3 _ (Subtype.ext s));
  have ho : ∀ {α β : ordinal}, (α ^ β).val = (ord_pow α)[[β.val]] := rfl;
  apply Subtype.ext; rw [ho]; conv => lhs; rw [ord_pow_setn0 h];
  rw [trans_func_rec2];
  have h2 := ord_pow_h_value α (⟨value (trans_rec_func (ord_pow_h α) (succ_set s0)) β.val,
    ord_pow_is_ord2 _ _⟩); unfold_projs at h2; simp only at h2;
  conv => lhs; unfold_projs; erw [h2]; simp only;
  unfold_projs; unfold ord_pow; simp only [h, ↓reduceIte];
theorem ord_pow3 {α β : ordinal} : α ≠ o0 → β ∈ K2 → α ^ β = ⋃(γ oo∈ β, α ^ γ) := by
  intro h0 h; apply Subtype.ext; unfold_projs; simp only;
  unfold ord_pow; simp only [h0, ↓reduceIte];
  erw [←ordinal_union_axiom, ←ord_pow_set3 _ _ h]; rfl;

@[simp] theorem ord_one_pow {α : ordinal} : o1 ^ α = o1 := by
  have h0 : o1 ≠ o0;
  · intro h; have h1 := @ord_lt_succ o0; rw [←o1, h] at h1; exact belong_to_self h1;
  apply ordinal.induction α; intro α h;
  cases k12 α with
  | inl h1 => cases h1 with
    | inl => subst α; simp;
    | inr h1 =>
      rcases h1 with ⟨β, h1⟩; subst α; have h1 := h _ ord_lt_succ;
      rw [ord_pow2, h1]; simp;
  | inr h1 =>
    rw [ord_pow3 h0 h1, ordinal_union_replace h];
    apply Subtype.ext; rw [←ordinal_union_axiom];
    rw [ordinal_replacement_const]; · exact union_one_element_set;
    exact ord_ne_0_gt_iff.2 (ord_k2_gt_0 h1);

theorem ord_pow_gt_0 {α β : ordinal} : o0 < α → o0 < α ^ β := by
  intro h0; apply ordinal.induction β; intro β h;
  cases k12 β with
  | inl h1 => cases h1 with
    | inl => subst β; simp only [ord_pow1]; exact ord_lt_succ;
    | inr h1 =>
      rcases h1 with ⟨γ, h1⟩; subst β; rw [ord_pow2];
      have h2 := h _ ord_lt_succ; rw [ord_succ_belong_le_iff] at h2;
      apply ord_lt_le_trans h0; conv => lhs; rw [←@ord_one_mul α];
      exact ord_le_right_mul h2;
  | inr h1 =>
    rw [ord_pow3 (ord_ne_0_gt_iff.2 h0) h1]; apply ord_lt_le_trans ord_lt_succ;
    rw [←o1, ←ord_pow1]; apply ord_union_le_sup; exact ord_k2_gt_0 h1;
theorem ord_lt_left_pow {α β γ : ordinal} : o1 < γ → α < β → γ ^ α < γ ^ β := by
  intro h0 h1; have hh : ∀ {α : ordinal}, γ ^ α < γ ^ (succ α);
  · intro α; have h2 := ord_lt_left_mul.1 ⟨@ord_pow_gt_0 _ α (ord_lt_trans ord_lt_succ h0), h0⟩;
    simp only [o1, ord_mul2, ord_mul1, ord_zero_add] at h2; rw [ord_pow2]; assumption;
  have h1 := ord_sub (ord_succ_belong_le_iff.1 h1); rcases h1 with ⟨β', h1, _⟩;
  subst β; apply ordinal.induction β'; intro β h; cases k12 β with
  | inl h2 => cases h2 with
    | inl =>
      subst β; simp only [ord_add1, gt_iff_lt]; exact hh;
    | inr h2 =>
      rcases h2 with ⟨δ, _⟩; subst β; rw [ord_add2];
      apply ord_lt_trans (h _ ord_lt_succ); exact hh;
  | inr h2 =>
    have b1 := @ord_add_k2_in_k2 (succ α) _ h2;
    rw [ord_pow3 (ord_ne_0_gt_iff.2 (ord_lt_trans ord_lt_succ h0)) b1];
    apply ord_lt_le_trans hh; apply ord_union_le_sup;
    conv => lhs; rw [←@ord_add1 (succ α)];
    apply ord_lt_left_add; exact ord_k2_gt_0 h2;
theorem ord_lt_left_pow_iff {α β γ : ordinal} : o1 < γ → (α < β ↔ γ ^ α < γ ^ β) := by
  intro h; constructor; · exact ord_lt_left_pow h;
  intro h1; rw [←ord_nle] at h1; rw [←ord_nle]; intro h0; apply h1;
  rw [ord_le] at h0; rw [ord_le]; cases h0 with
  | inl h0 => left; exact ord_lt_left_pow h h0;
  | inr => subst α; simp only [lt_self_iff_false, or_true];
theorem ord_le_left_pow_iff {α β γ : ordinal} : o1 < γ → (α ≤ β ↔ γ ^ α ≤ γ ^ β) := by
  intro h1; rw [←ord_nlt, ←ord_nlt]; have h := @ord_lt_left_pow_iff β α _ h1;
  revert h; aesop;
theorem ord_le_left_pow {α β γ : ordinal} : o0 < γ → α ≤ β → γ ^ α ≤ γ ^ β := by
  intro h; rw [ord_succ_belong_le_iff, ←o1, ord_le] at h; cases h with
  | inl h => exact (ord_le_left_pow_iff h).1;
  | inr => subst γ; simp;

theorem ord_lt_le_right_pow {α β γ : ordinal} : α < β → α ^ γ ≤ β ^ γ := by
  intro h; apply ordinal.induction γ; intro γ;
  cases k12 γ with
  | inl h1 => cases h1 with
    | inl => subst γ; simp;
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst γ; simp only [ord_pow2]; intro h1;
      have h2 : o0 < β ^ δ := ord_pow_gt_0 (ord_le_lt_trans ord_ge_0 h);
      apply ord_lt_le;
      exact ord_le_lt_trans (ord_le_right_mul (h1 _ ord_lt_succ))
        (ord_lt_left_mul.1 ⟨h2, h⟩);
  | inr h1 =>
    intro h0; by_cases h2 : α = o0;
    · subst α; rw [ord_pow01 (ord_ne_0_gt_iff.2 (ord_k2_gt_0 h1))]; exact ord_ge_0;
    have h3 : ¬β = o0;
    · rw [ord_ne_0_gt_iff] at *; exact ord_lt_trans h2 h;
    rw [ord_pow3 h2 h1, ord_pow3 h3 h1]; apply ord_union_sup_le;
    intro δ hd; apply ord_le_trans (h0 _ hd); exact ord_union_le_sup _ hd;
theorem ord_le_right_pow {α β γ : ordinal} : α ≤ β → α ^ γ ≤ β ^ γ := by
  intro h; rw [ord_le] at h; cases h with
  | inl h => exact ord_lt_le_right_pow h;
  | inr h => rw [h];
theorem ord_lt_right_pow_succ {α β γ : ordinal} : α < β → α ^ (succ γ) < β ^ (succ γ) := by
  intro h; have h1 := @ord_lt_le_right_pow _ _ γ h;
  have h2 : o0 < β ^ γ := ord_pow_gt_0 (ord_le_lt_trans ord_ge_0 h);
  simp only [ord_pow2]; exact ord_le_lt_trans (ord_le_right_mul h1)
        (ord_lt_left_mul.1 ⟨h2, h⟩)

theorem ord_le_pow {α β : ordinal} : o1 < α → β ≤ α ^ β := by
  intro h; apply ordinal.induction β; intro β h2;
  cases k12 β with
  | inl h1 => cases h1 with
    | inl => subst β; exact ord_ge_0;
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst β;
      apply ord_le_trans (ord_succ_le_succ (h2 _ ord_lt_succ));
      apply ord_succ_belong_le; exact ord_lt_left_pow h ord_lt_succ;
  | inr h1 =>
    rw [ord_pow3 (ord_ne_0_gt_iff.2 (ord_lt_trans ord_lt_succ h)) h1];
    intro γ hg; let γ : ordinal := ⟨γ, ord_element_ord _ _ hg⟩;
    convert_to γ < _; · rfl;
    apply ord_union_le_sup (succ γ) (ord_k2_succ_in h1 hg);
    exact (ord_lt_le_trans ord_lt_succ (h2 _ (ord_k2_succ_in h1 hg)));
theorem ord_lt_k2_pow {α β γ : ordinal} : β ∈ K2 → γ < α ^ β → ∃ δ, δ < β ∧ γ < α ^ δ := by
  intro h1 h2; have h3 : α ≠ o0;
  · by_contra; subst α; rw [ord_pow01 (ord_ne_0_gt_iff.2 (ord_k2_gt_0 h1))] at h2;
    exact belong_to_self (ord_lt_le_trans h2 ord_ge_0);
  rw [ord_pow3 h3 h1] at h2; exact ord_lt_union h2;

theorem ord_log {α β : ordinal} : o1 < α → o0 < β → ∃!δ, α ^ δ ≤ β ∧ β < α ^ (succ δ) := by
  intro ha hb; have h0 : ∃ γ : ordinal, β < α ^ γ;
  · use succ β; apply ord_le_lt_trans (ord_le_pow ha); exact ord_lt_left_pow ha ord_lt_succ;
  rcases minimal_ordinal h0 with ⟨γ, h1, h2⟩;
  have ha1 : α ≠ o0 := ord_ne_0_gt_iff.2 (ord_lt_trans ord_lt_succ ha);
  have h3 : γ ∉ K2;
  · by_contra h3; rw [ord_pow3 ha1 h3] at h1;
    rcases ord_lt_union h1 with ⟨δ, h4, h5⟩; have h6 := h2 _ h5;
    exact belong_to_self (ord_lt_le_trans h4 h6);
  rw [ord_in_k2] at h3; simp only [not_exists, not_and, not_forall, not_not] at h3; have h4 : _;
  · apply h3; intro h3; subst γ; simp only [ord_pow1] at h1; exact ord_no_between_succ ⟨hb, h1⟩;
  rcases h4 with ⟨δ, h4⟩; subst γ; use δ; simp only;
  have h4 : α ^ δ ≤ β; · rw [←ord_nlt]; intro h4; exact ord_nlt.2 (h2 _ h4) ord_lt_succ;
  use ⟨h4, h1⟩; intro γ ⟨g1, g2⟩;
  suffices g0 : ∀ δ γ : ordinal, δ < γ → β < α ^ (succ δ) → α ^ γ ≤ β → False;
  · apply ord_le_antisymm <;> rw [←ord_nlt] <;> intro d <;>
    apply g0 _ _ d <;> assumption';
  intro δ γ g3 h1 g1; rw [ord_succ_belong_le_iff] at g3;
  exact belong_to_self (calc
    β < α ^ succ δ        := h1
    _ ≤ α ^ γ             := (ord_le_left_pow_iff ha).1 g3
    _ ≤ β                 := g1
  )

theorem ord_pow_k2_in_k2 {α β : ordinal} : o1 < α → β ∈ K2 → α ^ β ∈ K2 := by
  intro h1 h2; cases k12 _ with
  | inr => assumption;
  | inl h => exfalso; cases h with
    | inl h =>
      revert h; simp only [imp_false]; rw [ord_ne_0_gt_iff]; apply ord_pow_gt_0;
      exact ord_lt_trans ord_lt_succ h1;
    | inr h =>
      rcases h with ⟨δ, h⟩;
      have h3 := ord_pow3 (ord_ne_0_gt_iff.2 (ord_lt_trans ord_lt_succ h1)) h2;
      rw [h3] at h; have d := @ord_lt_succ δ; rw [←h] at d;
      rcases ord_lt_union d with ⟨γ, d1, d2⟩;
      exact belong_to_self (calc
        succ δ  ≤ α ^ γ         := ord_succ_belong_le d2
        _       < α ^ (succ γ)  := ord_lt_left_pow h1 ord_lt_succ
        _       < α ^ β         := ord_lt_left_pow h1 (ord_k2_succ_in h2 d1)
        _       = succ δ        := by rw [h3, h]
      )
theorem ord_k2_pow_in_k2 {α β : ordinal} : α ∈ K2 → o0 < β → α ^ β ∈ K2 := by
  intro h1 h2; cases k12 β with
  | inr h => exact ord_pow_k2_in_k2 (ord_k2_succ_in h1 (ord_k2_gt_0 h1)) h;
  | inl h => cases h with
    | inl h => subst β; exfalso; exact belong_to_self h2;
    | inr h =>
      rcases h with ⟨γ, h⟩; subst β; rw [ord_pow2]; exact ord_mul_k2_in_k2
        (ord_ne_0_gt_iff.2 (ord_pow_gt_0 (ord_k2_gt_0 h1))) h1;

theorem ord_pow_add {α β γ : ordinal} : α ^ (β + γ) = α ^ β * α ^ γ := by
  apply ordinal.induction γ; intro γ h; cases k12 γ with
  | inl h1 => cases h1 with
    | inl => subst γ; simp only [ord_add1, ord_pow1, o1, ord_mul2, ord_mul1, ord_zero_add];
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst γ;
      rw [ord_add2, ord_pow2, ord_pow2, h _ ord_lt_succ]; symm; exact ord_mul_assoc;
  | inr h1 =>
    by_cases h2 : α = o0;
    · subst α; rw [ord_pow01 (ord_ne_0_gt_iff.2 (ord_k2_gt_0 h1))];
      rw [ord_pow01 (ord_ne_0_gt_iff.2 (ord_k2_gt_0 (ord_add_k2_in_k2 h1)))];
      simp only [ord_mul1];
    have h2' := h2; rw [ord_ne_0_gt_iff, ord_succ_belong_le_iff, ←o1, ord_le] at h2;
    cases h2 with
    | inr => subst α; simp only [ord_one_pow, ord_one_mul];
    | inl h2 =>
      have h3 := ord_pow_k2_in_k2 h2 h1; rw [ord_mul3 h3, ord_pow3 h2' (ord_add_k2_in_k2 h1)];
      apply ord_le_antisymm;
      · rw [ord_le_all_lt]; intro d d1; rcases ord_lt_union d1 with ⟨η, d1, d2⟩;
        apply ord_lt_le_trans d2; by_cases d3 : η < β;
        · exact ord_lt_le (calc
          α ^ η < α ^ β       := ord_lt_left_pow h2 d3
          _     = α ^ β * o1  := by simp [o1]
          _     ≤ _           := ord_union_le_sup o1 (ord_k2_succ_in h3 (ord_k2_gt_0 h3)))
        rw [ord_nlt] at d3; rcases ord_sub d3 with ⟨δ, d3, _⟩;
        subst η; rw [←ord_lt_add_left_elim] at d1; rw [h _ d1];
        exact ord_union_le_sup _ (ord_lt_left_pow h2 d1);
      rw [ord_le_all_lt]; intro d d1; rcases ord_lt_union d1 with ⟨δ, d1, d2⟩;
      apply ord_lt_le_trans d2; rcases ord_lt_k2_pow h1 d1 with ⟨τ, d3, d4⟩;
      apply ord_lt_le; apply ord_lt_le_trans;
      · rw [←ord_lt_left_mul]; use ord_pow_gt_0 (ord_ne_0_gt h2');
      rw [←h _ d3]; apply ord_union_le_sup; exact ord_lt_left_add d3;
theorem ord_pow_mul {α β γ : ordinal} : α ^ (β * γ) = (α ^ β) ^ γ := by
  apply ordinal.induction γ; intro γ h; cases k12 γ with
  | inl h1 => cases h1 with
    | inl => subst γ; simp only [ord_mul1, ord_pow1];
    | inr h1 =>
      rcases h1 with ⟨δ, h1⟩; subst γ;
      rw [ord_mul2, ord_pow2, ord_pow_add, h _ ord_lt_succ];
  | inr h1 =>
    by_cases h2 : β = o0;
    · subst β; simp only [ord_zero_mul, ord_pow1, ord_one_pow];
    have h3 := ord_mul_k2_in_k2 h2 h1; by_cases h4 : α = o0;
    · subst α; rw [ord_pow01 (ord_ne_0_gt_iff.2 (ord_k2_gt_0 h3))];
      rw [ord_pow01 h2]; rw [ord_pow01 (ord_ne_0_gt_iff.2 (ord_k2_gt_0 h1))];
    have h5 := ord_ne_0_gt_iff.2 (@ord_pow_gt_0 _ β (ord_ne_0_gt h4));
    rw [ord_pow3 h4 h3, ord_pow3 h5 h1];
    apply ord_le_antisymm <;> rw [ord_le_all_lt] <;> intro d d1 <;>
    rcases ord_lt_union d1 with ⟨δ, d1, d2⟩ <;> apply ord_lt_le_trans d2;
    · rcases ord_div h1 d1 with ⟨η, d3, d4⟩; exact (calc
        _ ≤ α ^ (β * η)     := ord_le_left_pow (ord_ne_0_gt h4) (ord_lt_le d4)
        _ = (α ^ β) ^ η     := h _ d3
        _ ≤ _               := ord_union_le_sup _ d3)
    rw [←h _ d1]; apply ord_union_le_sup; apply ord_lt_left_mul.1;
    use ord_ne_0_gt h2;

end zfset
