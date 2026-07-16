import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals

namespace zfset

def equiv (A B) := ∃ f : set, f f: A -1-1onto-> B
infix:80 " s≅ " => equiv

@[refl] theorem eqv_refl {a : set} : a s≅ a := by
  have h : (I Γ a).is_set := restrict_is_set ⟨id_one_one.1, id_one_one.2.1⟩;
  use (I Γ a).to_set h; unfold Fnc₂_on;
  rw [class_to_set_func2, class_to_set_domain, class_to_set_range];
  constructor; constructor;
  · exact ⟨relation_restrict, one_one_restrict id_one_one.2⟩;
  symm; all_goals
    rw [←extensionality_belong]; intro x; rw [Class_to_set_ext];
    first | rw [has_function.proof_domain]; | rw [has_function.proof_range];
    conv =>
      lhs; rhs; ext; rw [pair_in_restrict]; lhs; unfold I;
      rw [proof_in_Class]; simp;
    simp;
@[symm] theorem eqv_symm {a b : set} : a s≅ b → b s≅ a := by
  intro ⟨f, ⟨h1, h2⟩, h3⟩;
  use f⁻¹; constructor; constructor;
  · use inverse_is_relation; use h1.2.2;
    rw [rel_inv_inv_eq h1.1]; use h1.2.1;
  · rw [domain_inv, h3];
  · rw [range_inv, h2];
theorem eqv_comm {a b : set} : a s≅ b ↔ b s≅ a := Iff.intro eqv_symm eqv_symm
@[trans] theorem eqv_trans {a b : set} : a s≅ b → b s≅ c → a s≅ c := by
  intro ⟨f1, ⟨h1, h2⟩, h3⟩ ⟨f2, ⟨h4, h5⟩, h6⟩; use f1 ∘ f2; constructor;
  constructor; · exact ⟨congr_relation, congr_unitary2 h1.2 h4.2⟩;
  symm; all_goals
    first | rw [h2]; | rw [←h6];;
    rw [←extensionality_belong]; intro x;
    first |
      iterate 2 (rw [has_function.proof_domain];); |
      iterate 2 (rw [has_function.proof_range];);
    conv => lhs; rhs; ext; rw [has_function.proof_congr]; simp;
    constructor <;> intro ⟨x1, h⟩; rcases h with ⟨y, h7, h8⟩; use y;
    rw [exists_comm]; use x1; simp only [h, true_and, and_true];
  · rw [←has_function.proof_domain, ←h5, ←h3, has_function.proof_range]; use x;
  · rw [←has_function.proof_range, h3, h5, has_function.proof_domain]; use x;

theorem power_not_eqv {a : set} : ¬(a s≅ P(a)) := by
  intro ⟨f, ⟨h1, h2⟩, h3⟩;
  have h := axiom_of_separation a (fun b ↦ b ∉ f[[b]]);
  have h4 : (make_separation a fun b ↦ b ∉ (f[[b]])) s⊆ a;
  · intro x; have h := h x; simp only [intersection_def] at h;
    rw [←set_belong_set_to_class] at h; intro h0; exact (h.1 h0).1
  rw [←axiom_of_power] at h4; rw [←domain_inv] at h3;
  rw [←h3, has_function.proof_domain] at h4; rcases h4 with ⟨y, h4⟩;
  rw [pair_in_inverse] at h4; have h5 := value_func h1.2.1 h4;
  have h6 := h y; rw [←h5] at h6; simp only [intersection_def] at h6;
  rw [←set_belong_set_to_class] at h6; rw [proof_in_Class] at h6;
  have h7 := (has_function.proof_domain y).2 ⟨_, h4⟩; rw [←h2] at h7;
  have h8 := Iff.intro (fun a => (h6.1 a).2) (fun a => h6.2 ⟨h7, a⟩)
  simp at h8;
open Classical in
theorem Cantor {a b c d : set} : a s≅ c → c s⊆ b → b s≅ d → d s⊆ a → a s≅ b := by
  intro ⟨f, ha1, ha2⟩ hc ⟨g, hb1, hb2⟩ hd;
  rcases @omega_recursion (fun c => ∃ x, c = s⟨x, (f ∘ g)[x]⟩) (a - d)
    with ⟨h, ⟨h1, h2, h3⟩, _⟩;
  conv at h3 => rhs; rhs; rhs; lhs; ext; rw [←to_func];
  conv at h3 => rhs; rhs; rhs; rw [to_func_eq_value];
  have hn : ∀ n o∈ ω, h[[n.val]] s⊆ a;
  · apply nat_induction;
    · rw [h2]; intro x; rw [set_sub_is_sub]; exact And.left;
    intro i hi1 hi2; rw [h3 i hi1]; rw [←hb2] at hd;
    exact subseteq_trans (subseteq_trans restrict_range congr_range) hd;
  have hn2 : ∀ (n : ordinal), n ∈ ω → f[h[[n.val]]] s⊆ b;
  · intro n hx; rw [←ha2] at hc; exact subseteq_trans restrict_range hc;
  let s : Class := fun c ↦ ∃ x, x ∈ a ∧ c = s⟨x, if ∃ n o∈ ω, x ∈ h[[n.val]] then
      f[[x]] else g⁻¹[[x]]⟩;
  have hf : D(s) = a;
  · rw [←extensionality_belong]; intro z; unfold s;
    rw [has_function.proof_domain];
    conv => lhs; rhs; ext; rw [proof_in_Class];
    simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and, exists_eq_right];
    exact set_belong_set_to_class;
  have hs : D(s).is_set; · rw [hf]; exact set_to_Class_is_set;
  have hf1 : Fnc(s);
  · constructor;
    · intro c; unfold s; rw [proof_in_Class];
      simp only [forall_exists_index, and_imp]; intro x hx hc; subst c;
      simp only [pair_in_product, set_in_allset, and_self];
    intro u v w ⟨hu, hv⟩; unfold s at hu hv; rw [proof_in_Class] at hu hv;
    simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and] at hu hv;
    rw [hu.2, hv.2];
  have hf2 := domain_is_set hf1 hs;
  have htm : ∀ x : set, (∀ n o∈ ω, ¬(x ∈ h[[n.val]])) → x ∈ a → x ∈ d;
  · intro x hx;
    have hv2 := hx o0 (ord_k2_gt_0 omega_in_K2);
    rw [h2, set_sub_is_sub] at hv2; simp only [not_and, Decidable.not_not] at hv2;
    exact hv2;
  use s.to_set hf2; constructor; constructor; constructor;
  · exact (class_to_set_func.2 hf1).1
  · use (class_to_set_func.2 hf1).2; intro u v w ⟨hu, hv⟩;
    rw [pair_in_inverse, Class_to_set_ext] at hu hv; unfold s at hu hv;
    rw [proof_in_Class] at hu hv;
    simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and] at hu hv;
    by_cases hu1 : ∃ n o∈ ω, v ∈ h[[n.val]] <;>
    simp only [hu1, ↓reduceIte] at hu <;>
    by_cases hv1 : ∃ n o∈ ω, w ∈ h[[n.val]] <;>
    simp only [hv1, ↓reduceIte] at hv <;>
    symm at hu hv <;> rw [Eq.comm] at hu hv;
    · rw [ha1.2, ←value_func_iff ha1.1.2.1, ←pair_in_inverse] at hu hv;
      exact ha1.1.2.2 _ _ _ ⟨hu, hv⟩;
    · push Not at hv1; rw [ha1.2, ←value_func_iff ha1.1.2.1] at hu;
      have hv2 := htm _ hv1 hv.2;
      rw [←hb2, ←domain_inv] at hv2;
      have hv := (value_func_iff hb1.1.2.2).2 ⟨hv.1, hv2⟩;
      rw [pair_in_inverse] at hv;
      have hu2 := pair_in_congr.2 ⟨_, hu, hv⟩;
      rcases hu1 with ⟨n, hu3, hu4⟩; have hu5 := h3 n hu3;
      exfalso; apply hv1 (succ n) (ord_k2_succ_in omega_in_K2 hu3);
      rw [hu5, has_function.proof_range]; use v; rw [pair_in_restrict];
      use hu2;
    · push Not at hu1; rw [ha1.2, ←value_func_iff ha1.1.2.1] at hv;
      have hu2 := htm _ hu1 hu.2;
      rw [←hb2, ←domain_inv] at hu2;
      have hu := (value_func_iff hb1.1.2.2).2 ⟨hu.1, hu2⟩;
      rw [pair_in_inverse] at hu;
      have hv2 := pair_in_congr.2 ⟨_, hv, hu⟩;
      rcases hv1 with ⟨n, hv3, hv4⟩; have hv5 := h3 n hv3;
      exfalso; apply hu1 (succ n) (ord_k2_succ_in omega_in_K2 hv3);
      rw [hv5, has_function.proof_range]; use w; rw [pair_in_restrict];
      use hv2;
    · push Not at hu1 hv1;
      have hv2 := htm _ hv1 hv.2;
      rw [←hb2, ←domain_inv] at hv2;
      have hv := (value_func_iff hb1.1.2.2).2 ⟨hv.1, hv2⟩;
      have hu2 := htm _ hu1 hu.2;
      have hu := And.intro hu.1 hu2;
      rw [←hb2, ←domain_inv] at hu2;
      have hu := (value_func_iff hb1.1.2.2).2 ⟨hu.1, hu2⟩;
      rw [pair_in_inverse] at hu hv;
      exact hb1.1.2.1 _ _ _ ⟨hu, hv⟩;
  · rw [←extensionality_belong]; intro y; rw [has_function.proof_domain];
    conv =>
      rhs; rhs; ext; rw [Class_to_set_ext]; unfold s; rw [proof_in_Class];
      simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and];
    simp only [↓existsAndEq, and_true];
  · rw [←extensionality_belong]; intro y; rw [has_function.proof_range];
    conv =>
      lhs; rhs; ext; rw [Class_to_set_ext]; unfold s; rw [proof_in_Class];
      simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and];
    constructor <;> intro hy;
    · rcases hy with ⟨x, hy1, hy2⟩;
      by_cases hy3 : ∃ n o∈ ω, x ∈ h[[n.val]] <;>
      simp only [hy3, ↓reduceIte] at hy2;
      · rw [ha1.2] at hy1; symm at hy2;
        have hu4 := (value_func_iff ha1.1.2.1).2 ⟨hy2, hy1⟩;
        apply hc; rw [←ha2]; rw [has_function.proof_range]; use x;
      push Not at hy3; have hy4 := htm _ hy3 hy1; symm at hy2; rw [←hb2] at hy4;
      rw [←domain_inv] at hy4;
      have hu4 := (value_func_iff hb1.1.2.2).2 ⟨hy2, hy4⟩;
      rw [hb1.2, has_function.proof_domain];
      rw [pair_in_inverse] at hu4; use x;
    by_cases hu1 : ∃ n o∈ ω, y ∈ f[h[[n.val]]];
    · rcases hu1 with ⟨n, hu1, hu2⟩; rw [has_function.proof_range] at hu2;
      rcases hu2 with ⟨x, hu2⟩; rw [pair_in_restrict] at hu2;
      have hu3 : ∃ n o∈ ω, x ∈ h[[n.val]] := ⟨n, hu1, hu2.2⟩;
      use x; simp only [hu3, ↓reduceIte]; use hn n hu1 x hu2.2; symm;
      exact value_func ha1.1.2.1 hu2.1;
    push Not at hu1; have hu2 : ∀ n o∈ ω, g[[y]] ∉ h[[n.val]];
    · by_contra hu2; push Not at hu2; rcases hu2 with ⟨n, hu2, hu3⟩;
      have hu4 : n ≠ o0;
      · intro; subst n; rw [h2] at hu3; rw [set_sub_is_sub] at hu3;
        rw [hb1.2] at hy; have hu5 := value_func2 hb1.1.2.1 hy;
        have hu3 := hu3.2; rw [←hb2, has_function.proof_range] at hu3;
        push Not at hu3; have hu3 := hu3 y; contradiction;
      have hu5 := ((axiom_of_infinity n.val).1 hu2).2; unfold K1 at hu5;
      rw [proof_in_Class] at hu5; rcases hu5 with ⟨_, hu5⟩;
      rw [or_iff_not_imp_left] at hu5;
      have hu5 := hu5 (fun h ↦ hu4 (Subtype.ext h)); rcases hu5 with ⟨m, hu5⟩;
      simp only [Subtype.coe_eta] at hu5; rw [hu5] at hu3 hu2;
      rw [h3 m (ord_lt_trans ord_lt_succ hu2)] at hu3;
      rw [has_function.proof_range] at hu3;
      rw [hb1.2] at hy;
      conv at hu3 =>
        rhs; ext; rw [pair_in_restrict]; lhs; rw [pair_in_congr]; rhs; ext; rhs;
        rw [value_func_un2 hb1.1.2 hy];
      simp at hu3; have hu6 := hu1 m (ord_lt_trans ord_lt_succ hu2);
      rw [has_function.proof_range] at hu6;
      conv at hu6 => rhs; rhs; ext; rw [pair_in_restrict];
      contradiction;
    use g[[y]]; constructor;
    · apply hd; rw [←hb2, has_function.proof_range]; use y;
      apply value_func2 hb1.1.2.1; rwa [←hb1.2];
    have hu3 : ¬∃ n o∈ ω, g[[y]] ∈ h[[n.val]]; · push Not; exact hu2;
    simp only [hu3, ↓reduceIte]; symm; apply value_func hb1.1.2.2;
    rw [pair_in_inverse]; rw [hb1.2] at hy; exact value_func2 hb1.1.2.1 hy;

theorem eqv_foundational {a b r f : set} (h : f f: a-1-1onto->b)
  (h1 : is_foundational r a) : is_foundational (((f⁻¹) ∘ r) ∘ f) b := by
  intro x hx; let fx := f⁻¹[x]; have ha : fx s⊆ a;
  · unfold fx; intro y; rw [has_function.proof_range]; intro ⟨y1, h1⟩;
    rw [pair_in_restrict, pair_in_inverse] at h1; rw [h.1.2];
    exact (has_function.proof_domain _).2 ⟨_, h1.1⟩;
  have hb : fx ≠ s0;
  · unfold fx; intro hy; rw [←h.2, ←domain_inv] at hx;
    have hz := inverse_image (inv_unitary2 h.1.1.2) hx.1; rw [hy] at hz;
    conv at hz =>
      lhs; rhs; rw [restrict_empty_set
      ⟨inverse_is_relation, (inv_unitary2 (inv_unitary2 h.1.1.2)).1⟩];
    rw [range_empty_set] at hz; symm at hz; exact hx.2 hz;
  rcases h1 fx ⟨ha, hb⟩ with ⟨y, hy1, hy2⟩;
  unfold fx at hy1 hy2; rw [has_function.proof_range] at hy1;
  rcases hy1 with ⟨x1, hy1⟩; use x1;
  simp only [pair_in_restrict] at hy1; use hy1.2;
  have h0 : s0 = f[s0];
  · rw [restrict_empty_set, range_empty_set]; · exact ⟨h.1.1.1, h.1.1.2.1⟩;
  rw [h0, ←hy2, image_intersection h.1.1.2.2];
  conv => rhs; lhs; rhs; lhs; rw [←rel_inv_inv_eq h.1.1.1];
  rw [inverse_image (inv_unitary2 h.1.1.2)]; swap;
  · rw [domain_inv, h.2]; use hx.1;
  congr 1; simp only [congr_inv, congr_value, rel_inv_inv_eq h.1.1.1];
  congr; rw [←extensionality_belong]; intro a; simp only [element_in_one_element_set];
  rw [has_function.proof_range];
  conv =>
    lhs; rhs; ext;
    simp only [pair_in_restrict, element_in_one_element_set, pair_in_inverse];
  simp only [↓existsAndEq, and_true]; constructor;
  · intro ha; rw [←pair_in_inverse] at ha; exact h.1.1.2.2 _ _ _ ⟨ha, hy1.1⟩;
  rw [pair_in_inverse] at hy1; intro; subst a; use hy1.1;
theorem eqv_well_order {a b r f : set} (h : f f: a-1-1onto->b)
  (h1 : is_well_order r a) : is_well_order (((f⁻¹) ∘ r) ∘ f) b := by
  use eqv_foundational h h1.1;
  intro x hx y hy; simp only [pair_in_congr, pair_in_inverse];
  have hx' := hx; rw [←h.2, ←domain_inv] at hx;
  have ha1 := value_func2 h.1.1.2.2 hx; rw [pair_in_inverse] at ha1;
  have ha2 := (has_function.proof_domain _).2 ⟨_, ha1⟩; rw [←h.1.2] at ha2;
  have hy' := hy; rw [←h.2, ←domain_inv] at hy;
  have hb1 := value_func2 h.1.1.2.2 hy; rw [pair_in_inverse] at hb1;
  have hb2 := (has_function.proof_domain _).2 ⟨_, hb1⟩; rw [←h.1.2] at hb2;
  have h2 := h1.2 (f⁻¹[[x]]) ha2 (f⁻¹[[y]]) hb2; simp only at h2;
  cases h2 with
  | inl h2 =>
    left; use (f⁻¹[[y]]); constructor; · use (f⁻¹[[x]]);
    assumption;
  | inr h2 => cases h2 with
    | inl h2 =>
      right; left; rw [←h2] at hb1; exact h.1.1.2.1 _ _ _ ⟨ha1, hb1⟩;
    | inr h2 =>
    right; right; use (f⁻¹[[x]]); constructor; · use (f⁻¹[[y]]);
    assumption;
theorem eqv_ord_well_order {a : set} {α : ordinal} (h : α.val s≅ a) :
  ∃ r : set, is_well_order r a := by
  rcases h with ⟨f, h⟩;
  have he := well_order_restrict (E_well_order_ord α);
  have h2 := eqv_well_order h he; aesop;

open Classical in
noncomputable def card (a : set) : ordinal :=
  if h : ∃ α : ordinal, α.val s≅ a then Classical.choose (minimal_ordinal h) else o0
notation "|" a "|" => card a
theorem card_def1 {a : set} (h : ∃ α : ordinal, α.val s≅ a) :
  |a|.val s≅ a ∧ ∀ (γ : ordinal), γ.val s≅ a → |a| ≤ γ := by
  have h1 : |a| = |a| := rfl; conv at h1 =>
    rhs; unfold card; simp [h];
  have h2 := Classical.choose_spec (minimal_ordinal h); rwa [←h1] at h2;
theorem card_def2 {a : set} (h : ¬∃ α : ordinal, α.val s≅ a) : |a| = o0 := by
  unfold card; simp [h];
theorem card_def_or (a : set) : |a| = o0 ∨ |a|.val s≅ a := by
  by_cases h : ∃ α : ordinal, α.val s≅ a; · right; exact (card_def1 h).1;
  · left; exact (card_def2 h);
theorem eqv_card {a : set} : |a|.val s≅ a ↔ ∃ α : ordinal, α.val s≅ a := by
  constructor <;> intro h; · use card a;
  unfold card; simp only [h, ↓reduceDIte];
  have h1 := Classical.choose_spec (minimal_ordinal h); exact h1.1;
theorem eqv_card2 {a : set} : |a|.val s≅ a ↔ ∃ b : set, b s⊆ On ∧ b s≅ a := by
  constructor <;> intro h;
  · use |a|.val; use On_is_ordinal_class.1 _ |a|.prop;
  rw [eqv_card]; rcases h with ⟨b, h, h1⟩;
  let G : Class := fun c ↦ ∃ x y, c = s⟨x, y⟩ ∧ y ∈ b.to_Class - W(x) ∧
    (b.to_Class - W(x)) ∩ E⁻¹[s{y}] = s0;
  have f1 := @transfinite_recursion1 G;
  have f2 := fun α ↦ @transfinite_recursion2 G α (restrict_is_set f1.1);
  have h2 := @rec_choose_set b G (fun α ↦ restrict_is_set f1.1)
  have h2 : _;
  · apply h2; intro α ha;
    have h5 := @th7_482 b.to_Class E G ⟨E_well_founded, E_well_order_ord_class h⟩ rfl;
    have hax : trans_rec_class G Γ α = trans_rec_class G Γ α.val := rfl;
    conv at ha =>
      lhs; rhs; rhs; rw [hax, ←Class_to_set_to_Class (@restrict_is_set _ α.val f1.1)];
    rw [set_to_class_range] at ha;
    conv =>
      rhs; rhs; rhs; rw [hax, ←Class_to_set_to_Class (@restrict_is_set _ α.val f1.1)];
    rw [set_to_class_range]; exact (h5 _ ha).1;
  rcases h2 with ⟨α, h2, h3, h4⟩; use α; refine eqv_trans ?_ h1;
  use (trans_rec_class G Γ α).to_set (restrict_is_set f1.1); constructor; constructor;
  · use class_to_set_rel.2 (restrict_is_func f1.1).1;
    rwa [unitary2_to_Class, Class_to_set_to_Class_has_belong];
  · rw [class_to_set_domain]; conv => rhs; lhs; rw [domain_restrict, ←f1.2];
    rw [←extensionality_belong]; intro c;
    simp only [Class_to_set_ext, intersection_def, set_ord_belong, iff_and_self];
    exact ord_element_ord _ _;
  · rw [class_to_set_range]; conv => lhs; lhs; rw [h3];
    exact set_to_Class_to_set _;

theorem ord_eqv_card {α : ordinal} : |α.val|.val s≅ α.val := by
  rw [eqv_card]; use α;
theorem ord_card_le {α : ordinal} : |α.val| ≤ α := by
  have h : ∃ β : ordinal, β.val s≅ α.val := ⟨α, eqv_refl⟩;
  unfold card; simp only [h, ↓reduceDIte, ge_iff_le];
  have h3 := Classical.choose_spec (minimal_ordinal h);
  apply h3.2; rfl;
theorem eqv_card_eq {a b : set} : a s≅ b → |a| = |b| := by
  intro h0; by_cases h : ∃ α : ordinal, α.val s≅ a;
  · have h' := h; rcases h with ⟨α, h⟩;
    have h2 : ∃ α : ordinal, α.val s≅ b := ⟨α, eqv_trans h h0⟩
    unfold card; simp only [h', ↓reduceDIte, h2];
    have h3 := Classical.choose_spec (minimal_ordinal h');
    have h4 := Classical.choose_spec (minimal_ordinal h2);
    apply ord_le_antisymm; · apply h3.2; exact eqv_trans h4.1 (eqv_symm h0);
    apply h4.2; exact eqv_trans h3.1 h0;
  have h2 : ¬∃ α : ordinal, α.val s≅ b :=
    fun ⟨α, ha⟩ ↦ h ⟨α, eqv_trans ha (eqv_symm h0)⟩;
  unfold card; simp only [h, ↓reduceDIte, h2];

@[simp] theorem card_0 : |s0| = o0 := by
  have h : ∃ α : ordinal, α.val s≅ s0 := ⟨o0, eqv_refl⟩;
  have h1 := card_def1 h;
  have h2 := h1.2 o0 eqv_refl; exact ord_le_antisymm h2 ord_ge_0;
theorem card_card {a : set} : | |a|.val| = |a| := by
  by_cases h : ∃ α : ordinal, α.val s≅ a; swap;
  · have h0 := card_def2 h; simp only [h0]; exact card_0;
  rcases card_def1 h with ⟨h1, h2⟩;
  rcases card_def1 ⟨|a|, eqv_refl⟩ with ⟨h3, h4⟩;
  exact ord_le_antisymm (h4 _ eqv_refl) (h2 _ (eqv_trans h3 h1));

theorem foo (h : (A ∨ C) ↔ (B ∨ C)) (hA : C → ¬ A) (hB : C → ¬ B) : A ↔ B :=
Iff.intro
  (fun ha =>
    match h.mp (Or.inl ha) with
    | Or.inl hb => hb
    | Or.inr hc => False.elim (hA hc ha))
  (fun hb =>
    match h.mpr (Or.inl hb) with
    | Or.inl ha => ha
    | Or.inr hc => False.elim (hB hc hb))
theorem nat_eqv_eq' {m n : nat} : m.val.val s≅ n.val.val → m = n := by
  revert m; have h0 : ∀ {m : nat}, m.val.val s≅ n0.val.val → m = n0;
  · intro m ⟨f, ⟨h, h0⟩, h1⟩; rw [←range_inv] at h0; rw [←domain_inv] at h1;
    have h2 := domain_empty_set ⟨⟨inverse_is_relation, h.2.2⟩, Eq.symm h1⟩;
    rw [h2, range_empty_set] at h0; apply Subtype.ext; apply Subtype.ext; exact h0;
  apply nat.induction n; · assumption;
  intro n h m hh; have hm : m ≠ n0;
  · intro hm; subst m; have h1 := h0 (eqv_symm hh);
    exact peano3 _ (Subtype.coe_inj.2 h1);
  rcases hh with ⟨f, ⟨h1, h2⟩, h3⟩;
  have h4 := succ_subset_K1.1 m.prop _ ord_lt_succ; rcases h4 with ⟨_, h4⟩;
  rw [or_iff_not_imp_left] at h4;
  have h4 := h4 (fun a ↦ hm (Subtype.ext (Subtype.ext a))); rcases h4 with ⟨c, h4⟩;
  have h5 := Subtype.coe_inj.2 h4; simp only at h5; have h6 := m.prop;
  rw [ord_belong, h5] at h6; have h6 := ω.prop.1 _ h6 _ ord_lt_succ;
  let c : nat := ⟨c, h6⟩; have h5 := @Subtype.ext _ _ _ (succ_nat c) (Subtype.ext h5);
  have h6x : c.val ∈ D(f); · rw [←h2, h5]; exact ord_lt_succ;
  have h9 : ∀ c, (succ_nat c).val.val = succ_set c.val.val := fun c ↦ rfl;
  subst m; congr; apply h; by_cases g : f[[c.val.val]] = n.val.val;
  · use f Γ c.val.val; constructor; constructor;
    · use relation_restrict; exact one_one_restrict h1.2;
    · rw [domain_restrict, ←h2, intersection_comm, ←subseteq_iff_eq_intersection];
      apply ord_lt_le; exact ord_lt_succ;
    have h6 := range_eq_S h1.2.1 h6x; have h7 := range_nin_S h1.2 h6x;
    rw [←h2, h3, g] at h6; rw [←h2, g] at h7;
    have h8 : (succ_nat c).val.val - s{c.val.val} = c.val.val :=
      union_sub (belong_to_self);
    rw [h8] at h6 h7; rw [h9] at h6;
    have h10 : succ_set n.val.val - s{n.val.val} =
      W(f Γ c.val.val) ∪ s{n.val.val} - s{n.val.val}; · rw [h6];
    unfold succ_set at h10; rw [union_sub (belong_to_self), union_sub h7] at h10;
    symm; assumption;
  let fn := f[[c.val.val]]; let frn := f⁻¹[[n.val.val]];
  let fln := (f Γ (c.val.val - s{frn})) ∪ s{s⟨frn, fn⟩}; use fln;
  have flnf := @function_one_pair frn fn;
  have f1 : _ → Fnc(fln) := union_function (restrict_is_func ⟨h1.1, h1.2.1⟩) flnf.1;
  have f1 : _;
  · apply f1; rw [←extensionality_belong]; intro a;
    simp [←set_belong_set_to_class, has_function.proof_domain, set_sub_is_sub,
      empty_false];
  have f2 : Un₂(fln);
  · use f1.2; intro u v w ⟨hv, hw⟩; rw [pair_in_inverse] at hv hw; unfold fln at hv hw;
    simp only [binary_union_def, pair_in_restrict, set_sub_is_sub,
      element_in_one_element_set, ordered_pair_eq_iff] at hv hw; cases hv with
    | inl hv => cases hw with
      | inl hw => rw [←pair_in_inverse] at hv hw; exact h1.2.2 _ _ _ ⟨hv.1, hw.1⟩;
      | inr hw =>
        rcases hw with ⟨_, _⟩; subst w u; have hfc := value_func2 h1.2.1 h6x;
        unfold fn at hv; rw [←pair_in_inverse] at hv hfc;
        have hf2 := h1.2.2 _ _ _ ⟨hv.1, hfc⟩; subst v; exfalso;
        exact belong_to_self hv.2.1;
    | inr hv => cases hw with
      | inl hw =>
        rcases hv with ⟨_, _⟩; subst v u; have hfc := value_func2 h1.2.1 h6x;
        unfold fn at hw; rw [←pair_in_inverse] at hw hfc;
        have hf2 := h1.2.2 _ _ _ ⟨hw.1, hfc⟩; subst w; exfalso;
        exact belong_to_self hw.2.1;
      | inr hw => rw [hv.1, hw.1];
  have f3h : n.val ∈ W(f); · rw [h3]; exact ord_lt_succ;
  rw [←domain_inv] at f3h;
  have f3 := value_func2 h1.2.2 f3h; rw [pair_in_inverse] at f3;
  have f3' := value_func h1.2.1 f3;
  have hc1 : frn ∈ c.val.val;
  · unfold frn; have f4 : f⁻¹[[n.val.val]] ≠ c.val.val;
    · intro f4; rw [f4] at f3'; exact g f3';
    have f5 := (has_function.proof_domain _).2 ⟨_, f3⟩; rw [←h2, h9] at f5;
    unfold succ_set at f5;
    simp only [binary_union_def, element_in_one_element_set] at f5; cases f5 with
    | inl => assumption;
    | inr f5 => contradiction;
  constructor; constructor; constructor;
  · exact f1.1;
  · exact f2;
  · unfold fln; rw [domain_union, domain_restrict, ←function_one_pair.2];
    have hc : (c.val.val - s{frn}) s⊆ D(f);
    · intro x; rw [←h2, h9]; unfold succ_set; simp only [set_sub_is_sub,
      element_in_one_element_set, binary_union_def, and_imp];
      intro hx1 hx2; left; exact hx1;
    rw [subseteq_iff_eq_intersection, intersection_comm] at hc;
    rw [←hc]; rw [←extensionality_belong]; intro a; simp only [binary_union_comm,
      binary_union_def, element_in_one_element_set, set_sub_is_sub];
    constructor <;> intro fd;
    · by_cases a = frn; · left; assumption;
      · right; constructor <;> assumption;
    cases fd with
    | inl => subst a; assumption;
    | inr fd; exact fd.1;
  · unfold fln; rw [range_union, range_one_pair];
    have f3 : D(f) = (c.val.val - s{frn}) ∪ s{c.val.val} ∪ s{frn};
    · rw [←h2, h9]; unfold succ_set; rw [←extensionality_belong]; intro a;
      simp only [binary_union_def, element_in_one_element_set, binary_union_comm,
        set_sub_is_sub]; constructor <;> intro h;
      · by_cases fc : a = frn; · left; assumption;
        right; cases h with
        | inl => left; constructor <;> assumption;
        | inr => right; assumption;
      cases h with
      | inl => subst a; left; assumption;
      | inr h => cases h with
        | inl h => left; exact h.1;
        | inr => right; assumption;
    have f4 := restrict_to_domain h1.1; simp only [f3, restrict_to_union] at f4;
    have f5 : W(f) = W(f) := rfl; conv at f5 => rhs; rw [f4];
    simp only [range_union] at f5;
    rw [h3, h9] at f5; unfold succ_set at f5; rw [range_one_element h1.2.1,
      range_one_element h1.2.1] at f5; swap;
    · rw [←h2, h9]; unfold succ_set; simp only [binary_union_def]; left; assumption;
    swap; · assumption;
    unfold fn; conv at f5 => rhs; rhs; rhs; unfold frn; rw [f3'];
    rw [←extensionality_belong]; intro a; have f6 := extensionality_belong.2 f5 a;
    rw [binary_union_def, binary_union_def] at f6;
    simp only [element_in_one_element_set] at f6; symm;
    apply foo f6 <;> intro fc <;> subst a; · exact belong_to_self;
    intro h7; simp only [binary_union_def, element_in_one_element_set] at h7;
    cases h7 with
    | inr h7 => symm at h7; contradiction;
    | inl h7 =>
      simp only [has_function.proof_range, pair_in_restrict, set_sub_is_sub,
        element_in_one_element_set] at h7;
      rcases h7 with ⟨w, h7, h8, h9⟩; apply h9; unfold frn;
      rw [←pair_in_inverse] at h7; symm; exact value_func h1.2.2 h7;
theorem nat_eqv_eq {m n : ordinal} (hm : m < ω) (hn : n < ω) :
  m.val s≅ n.val → m = n :=
  fun h ↦ (@Subtype.coe_inj _ _ ⟨m, hm⟩ ⟨n, hn⟩).2 (nat_eqv_eq' h)

theorem nat_card {n : ordinal} (h : n < ω) : n = |n.val| := by
  have h2 := ord_le_lt_trans ord_card_le h;
  exact nat_eqv_eq h h2 (eqv_symm ord_eqv_card);
theorem ord_eqv_nat {α n : ordinal} (h : n < ω) : α.val s≅ n.val → α = n := by
  intro h1; cases @ord_total α ω with
  | inl h2 => exact nat_eqv_eq h2 h h1;
  | inr h2 =>
    symm at h2; conv at h2 => rhs; rw [Eq.comm];
    rw [←ord_le] at h2;
    have h5 := eqv_trans (Cantor eqv_refl (ord_succ_belong_le
      (ord_lt_le_trans h h2)) h1 (ord_lt_le (@ord_lt_succ n))) h1;
    have h3 := ord_k2_succ_in omega_in_K2 h;
    have h4 := nat_eqv_eq h3 h h5;
    have h6 := @ord_lt_succ n; rw [h4] at h6; exfalso; exact belong_to_self h6;

def finite (a : set) := ∃ n o∈ ω, a s≅ n.val
def infinite (a : set) := ¬(finite a)

def is_card (α) := ∃ x, α = |x|
def card_class : Class := fun s ↦ ∃ h : Ord(s), is_card ⟨s, h⟩
def cardinal := {α : ordinal // is_card α}
theorem cardinal_card {α : ordinal} : is_card α ↔ α = |α.val| := by
  constructor <;> intro h; swap; · use α.val;
  rcases h with ⟨x, h⟩; cases card_def_or x with
  | inl h1 => rw [h1] at h; subst α; symm; exact card_0;
  | inr h1 =>
    have h2 := @ord_eqv_card α; rw [←h] at h1; have h3 := eqv_trans h2 h1;
    have h4 := eqv_card_eq h3; rw [card_card, ←h] at h4; symm; exact h4;
theorem omega_sub_card {α : ordinal} (h : α < ω) : is_card α :=
  cardinal_card.2 (nat_card h)


end zfset
