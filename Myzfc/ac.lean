import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal

namespace zfset

def AC := ∀ a : set, ∃ f : set, ∀ x s∈ a, x ≠ s0 → f[[x]] ∈ x
def WOP := ∀ a : set, ∃ r : set, is_well_order r a
def GCH := ∀ a, ∀ b : set, b s⊆ P(a) → infinite a → (∃ x, a s⊆ x ∧ x s≅ b) → b s≅ a ∨ b s≅ P(a)

theorem AC_to_WOP (ac : AC) : WOP := by
  intro a; rcases ac P(a) with ⟨f, h⟩;
  let G : Class := to_func fun x ↦ f[[a - W(x)]];
  have h1 := @transfinite_recursion1 G;
  have h2 := fun α ↦ @transfinite_recursion2 G α
    (restrict_is_set h1.1);
  have h3 := @rec_choose_set a G (fun α ↦ restrict_is_set transfinite_recursion1.1);
  have h4 : _;
  · apply h3; intro α ha; conv => lhs; lhs; unfold G;
    rw [to_func_eq_value, class_sub_is_sub, ←set_belong_set_to_class];
    have hs : W(trans_rec_class G Γ α).is_set;
    · apply class_is_set_range; exact restrict_is_set h1.1;
    simp only; rw [←Class_to_set_ext hs, ←set_sub_is_sub];
    rw [class_to_set_range];
    apply h (a - W(trans_rec_class G Γ α).to_set hs);
    · rw [axiom_of_power]; intro x; rw [set_sub_is_sub]; exact fun h ↦ h.1;
    intro h0; apply ha; rw [←extensionality_belong]; intro x;
    rw [←set_belong_set_to_class, class_sub_is_sub, ←set_belong_set_to_class];
    simp only; conv => lhs; rhs; rhs; rw [←Class_to_set_ext hs];
    rw [←h0, set_sub_is_sub];
  rcases h4 with ⟨α, h4, h5, h6⟩; apply @eqv_ord_well_order _ α;
  use (trans_rec_class G Γ α).to_set (restrict_is_set h1.1); constructor; constructor;
  constructor;
  · rw [relation_to_Class, Class_to_set_to_Class_has_belong];
    exact (restrict_is_func h1.1).1;
  · rw [unitary2_to_Class, Class_to_set_to_Class_has_belong]; exact h6;
  · rw [class_to_set_domain]; have ha : On ∩ α = α.val.to_Class;
    · rw [←extensionality_belong]; intro x;
      simp only [intersection_def, ←set_belong_set_to_class, set_ord_belong];
      simp only [and_iff_right_iff_imp]; exact ord_element_ord _ _;
    conv => rhs; lhs; rw [domain_restrict, ←h1.2, ha];
    rw [set_to_Class_to_set];
  rw [class_to_set_range, ←extensionality_belong]; intro x;
  rw [Class_to_set_ext, h5, ←set_belong_set_to_class]
theorem WOP_to_AC (wop : WOP) : AC := by
  intro a; rcases wop ∪(a) with ⟨f, h1, h2⟩;
  have h4 := fun x hx h3 ↦ well_order_minimal ⟨h1, h2⟩ _ ⟨@unionset_subseteq _ _ _ _ _ a x hx, h3⟩;
  let f2 : Class := fun s ↦ ∃ x y : set, s = s⟨x, y⟩ ∧ x ∈ a ∧ x ≠ s0
       ∧ y ∈ x ∧ x ∩ W(f⁻¹ Γ s{y}) = s0;
  have hf : Fnc(f2);
  · constructor;
    · intro c hc; unfold f2 at hc; rw [proof_in_Class] at hc;
      rcases hc with ⟨x, y, hc, _⟩; subst c; simp;
    intro u v w ⟨hv, hw⟩; unfold f2 at hv hw; rw [proof_in_Class] at hv hw;
    simp only [ordered_pair_eq_iff, ne_eq, ↓existsAndEq, and_true,
      exists_eq_left'] at hv hw;
    rcases h4 _ hv.1 hv.2.1 with ⟨x, hv1, hv2⟩;
    have hw1 := hv2 _ hv.2.2; have hw2 := hv2 _ hw.2.2;
    subst v w; rfl;
  have hf : Fnc_on f2 (a - s{s0}).to_Class;
  · use hf; rw [←extensionality_belong]; intro x;
    simp only [set_sub_is_sub, ←set_belong_set_to_class, element_in_one_element_set];
    rw [has_function.proof_domain];
    conv =>
      rhs; rhs; ext; unfold f2; rw [proof_in_Class];
      simp only [ordered_pair_eq_iff, ne_eq, ↓existsAndEq, and_true, exists_eq_left'];
    constructor <;> intro hx;
    · rcases h4 _ hx.1 hx.2 with ⟨x1, h5, _⟩; use x1; use hx.1; use hx.2;
    rcases hx with ⟨_, hx1, hx2, _⟩; exact ⟨hx1, hx2⟩;
  have hf2 : D(f2).is_set; · rw [←hf.2]; exact set_to_Class_is_set;
  have hf3 := domain_is_set hf.1 hf2;
  use f2.to_set hf3; intro x hx1 hx2;
  have hf4 : x ∈ D(f2.to_set hf3);
  · rw [class_to_set_domain, Class_to_set_ext, ←hf.2, ←set_belong_set_to_class];
    rw [set_sub_is_sub]; simp only [element_in_one_element_set]; exact ⟨hx1, hx2⟩;
  have hf5 : Un(f2.to_set hf3);
  · rw [unitary_to_Class, Class_to_set_to_Class_has_belong]; use hf.1.2;
  have hf6 := value_func2 hf5 hf4; rw [Class_to_set_ext] at hf6;
  conv at hf6 => rhs; unfold f2;
  rw [proof_in_Class] at hf6; simp only [ordered_pair_eq_iff, ne_eq,
    ↓existsAndEq, and_true, exists_eq_left'] at hf6; exact hf6.2.2.1;
theorem AC_eq_WOP : AC ↔ WOP := Iff.intro AC_to_WOP WOP_to_AC

theorem eqv_ord [ac : Fact AC] {a : set} : ∃ α : ordinal, α.val s≅ a :=
  match AC_to_WOP ac.out a with | ⟨_, h⟩ => well_order_eqv_ord h
theorem all_eqv_card [ac : Fact AC] {a : set} : |a|.val s≅ a := eqv_card.2 eqv_ord
theorem card_o0_eq_s0 [ac : Fact AC] {a : set} : |a| = o0 ↔ a = s0 := by
  have h := @all_eqv_card _ a; constructor <;> intro h1;
  · rw [h1] at h; symm at h; exact eqv_s0_eq_s0 h;
  subst a; simp only [card_0];



end zfset
