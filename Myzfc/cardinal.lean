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
  congr 1; simp only [congr_inv, congr_image, rel_inv_inv_eq h.1.1.1];
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
theorem eqv_isom {a b r f : set} (h : f f: a-1-1onto->b) :
  Isom f r ((((f⁻¹) ∘ r) ∘ f)) a b := by
  constructor
  · exact h
  intro x hx y hy
  simp only [pair_in_congr, pair_in_inverse]
  constructor
  · intro hxy
    use y
    constructor
    · use x
      constructor
      · apply value_func2 h.1.1.2.1
        rw [←h.1.2]
        exact hx
      exact hxy
    apply value_func2 h.1.1.2.1
    rw [←h.1.2]
    exact hy
  intro hxy
  rcases hxy with ⟨z, hz1, hz2⟩
  rcases hz1 with ⟨u, hu1, hu2⟩
  have hxv := value_func h.1.1.2.1 hu1
  have hxv' : f[[x]] = f[[u]] := by
    rw [hxv]
  have hxu : x = u := by
    apply h.1.1.2.2
    constructor
    · rw [pair_in_inverse]
      apply value_func2 h.1.1.2.1
      rw [←h.1.2]
      exact hx
    · rw [pair_in_inverse]
      exact hu1
  have hyv := value_func h.1.1.2.1 hz2
  have hyv' : f[[y]] = f[[z]] := by
    rw [hyv]
  have hyz : y = z := by
    apply h.1.1.2.2
    constructor
    · rw [pair_in_inverse]
      apply value_func2 h.1.1.2.1
      rw [←h.1.2]
      exact hy
    · rw [pair_in_inverse]
      exact hz2
  rwa [←hxu, ←hyz] at hu2

theorem eqv_ord_well_order {a : set} {α : ordinal} (h : α.val s≅ a) :
  ∃ r : set, is_well_order r a := by
  rcases h with ⟨f, h⟩;
  have he := well_order_restrict (E_well_order_ord α);
  have h2 := eqv_well_order h he; aesop;
theorem well_order_eqv_ord [has_belong α] [has_intersection α Class] [has_value α]
  [has_intersection set α] [has_intersection Class α] {a : set} {R : α}
  (h : is_well_order R a) :
  ∃ α : ordinal, α.val s≅ a := by
  rcases ord_isom_we_set h with ⟨α, ⟨f, h1⟩, h2⟩; use α; use f; exact h1.1;

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
  rw [eqv_card]; rcases h with ⟨b, hbOn, hba⟩;
  have hwo : is_well_order E b := E_well_order_ord_class hbOn;
  rcases (ord_isom_we_set hwo) with ⟨β, ⟨f, hf⟩, _⟩;
  rcases hf with ⟨⟨⟨hf1, hf2⟩, hf3⟩, _⟩;
  use β;
  refine eqv_trans ?_ hba;
  use f; exact ⟨⟨hf1, hf2⟩, hf3⟩;
theorem isom_set_eqv [has_belong α] {a b f : set} {R1 R2 : α} (h : Isom f R1 R2 a b) :
  a s≅ b := ⟨f, h.1⟩
theorem eqv_image [has_belong α] [has_intersection α Class] [has_function α]
  [has_intersection α α]
  {f A B a : α} (h : f f: A-1-1onto->B) (h1 : a s⊆ A) : (f Γ a) f: a-1-1onto->f[a] := by
  simp only [and_true]; use ⟨relation_restrict, one_one_restrict h.1.1.2⟩;
  rwa [domain_restrict, ←h.1.2, intersection_comm, ←subseteq_iff_eq_intersection];

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
theorem eqv_ord_le {a} {α} (h : a s≅ α.val) : |a| ≤ α :=
  (card_def1 ⟨α, eqv_symm h⟩).2 _ (eqv_symm h)
theorem eqv_s0_eq_s0 {a} : a s≅ s0 → a = s0 := by
  rw [eqv_comm]; intro ⟨f, h1, h2⟩; have h3 := domain_empty_set ⟨⟨h1.1.1, h1.1.2.1⟩, h1.2⟩;
  subst f; symm; rwa [range_empty_set] at h2;

theorem one_set {a b : set} : s{a} s≅ s{b} := by
  use s{s⟨a, b⟩}; use func2_one_pair; exact range_one_pair;
theorem eqv_disjoint_union {a b c d : set} (h1 : a ∩ b = s0) (h2 : c ∩ d = s0)
  (h3 : a s≅ c) (h4 : b s≅ d) : (a ∪ b) s≅ (c ∪ d) := by
  rcases h3 with ⟨f, f1, f2⟩; rcases h4 with ⟨g, g1, g2⟩;
  use f ∪ g; constructor; constructor;
  · apply union_func2 f1.1 g1.1; · rw [←f1.2, ←g1.2, h1]; rfl;
    · rw [f2, g2, h2]; rfl;
  · rw [domain_union, ←f1.2, ←g1.2];
  · rw [range_union, ←f2, ←g2];
theorem omega_sub_0_eqv_omega : ω.val s≅ (ω.val - s{s0}) := by
  let f := {s⟨n.val, (succ n).val⟩ // n o∈ ω}; use f; constructor; constructor; constructor;
  · intro x hx; rw [mem_ordinal_replacement] at hx; rcases hx with ⟨_, _, _⟩; subst x; simp;
  · constructor <;> intro u v w ⟨h1, h2⟩; swap; rw [pair_in_inverse] at h1 h2;
    all_goals
      rw [mem_ordinal_replacement] at h1 h2; simp only [ordered_pair_eq_iff] at h1 h2;
      rcases h1 with ⟨a, ⟨_, _⟩, _⟩; rcases h2 with ⟨b, ⟨_, _⟩, _⟩; subst v w u;
      rw [Subtype.coe_inj] at *;
    · apply (@peano4 a b).1; assumption;
    congr;
  · rw [←extensionality_belong]; intro x; rw [has_function.proof_domain];
    conv => rhs; rhs; ext; rw [mem_ordinal_replacement];
            rhs; ext; rhs; rw [ord_belonged_to, belong_to_ordset];
    simp only [← set_ord_belong, ordered_pair_eq_iff, ↓existsAndEq, and_true]; constructor <;> intro h;
    · use ⟨x, ord_element_ord _ _ h⟩;
    aesop;
  · rw [←extensionality_belong]; intro x; rw [has_function.proof_range];
    conv => lhs; rhs; ext; rw [mem_ordinal_replacement];
            rhs; ext; rhs; rw [ord_belonged_to, belong_to_ordset];
    simp only [ordered_pair_eq_iff, ↓existsAndEq, true_and]; constructor <;> intro h;
    · rcases h with ⟨y, h1, h2⟩; subst x; rw [set_sub_is_sub]; use ord_k2_succ_in omega_in_K2 h2;
      simp only [element_in_one_element_set]; intro h3; apply peano3; apply Subtype.ext; exact h3;
    · rw [set_sub_is_sub] at h; simp only [element_in_one_element_set] at h; rcases h with ⟨h1, h2⟩;
      let x : ordinal := ⟨x, ord_element_ord _ _ h1⟩;
      have h1' := @nat_two_type x h1; rw [or_iff_not_imp_left] at h1';
      have h3 := fun a ↦ h2 ((@Subtype.coe_inj _ _ x o0).2 a); have h3 := h1' h3;
      rcases h3 with ⟨y, h3⟩; use y; use Subtype.coe_inj.2 h3; have h1 : x ∈ ω := h1;
      rw [h3] at h1; exact ord_lt_trans ord_lt_succ h1;

theorem omega_add_one_eqv_omega {a} (h : a ∉ ω) : (ω.val ∪ s{a}) s≅ ω.val := by
  suffices h1 : ω.val = (ω.val - s{s0}) ∪ s{s0};
  · conv => rhs; rw [h1];
    apply eqv_disjoint_union;
    · rw [←extensionality_belong]; intro b; simp only [intersection_def,
      element_in_one_element_set, empty_false, iff_false, not_and];
      intro c d; apply h; subst b; exact c;
    · rw [←extensionality_belong]; intro b; simp only [intersection_comm, intersection_def,
      element_in_one_element_set, set_sub_is_sub, empty_false, iff_false, not_and, not_not];
      exact fun c _ ↦ c;
    · exact omega_sub_0_eqv_omega;
    · exact one_set;
  rw [←extensionality_belong]; intro b; simp only [binary_union_comm, binary_union_def,
    element_in_one_element_set, set_sub_is_sub];
  apply Iff.intro;
  · intro a_1; simp_all only [true_and]; exact Classical.em _;
  · intro a_1; cases a_1 with
    | inl h_1 => subst h_1; exact peano1;
    | inr h_2 => simp_all only;
theorem inf_ord_eqv_add_one {a : ordinal} (h : ω ≤ a) : (succ a).val s≅ a.val := by
  suffices h1 : a.val = (a.val - ω.val) ∪ ω.val;
  · suffices h2 : (succ a).val = (a.val - ω.val) ∪ (ω.val ∪ s{a.val});
    · rw [h1, h2]; apply eqv_disjoint_union;
      · rw [←extensionality_belong]; intro b; simp only [intersection_def, set_sub_is_sub,
        binary_union_def, element_in_one_element_set, empty_false, iff_false, not_and, not_or,
        and_imp]; intro c d; use d; intro e; subst b; exact belong_to_self c;
      · rw [←extensionality_belong]; intro b; simp only [intersection_comm, intersection_def,
        set_sub_is_sub, empty_false, iff_false, not_and, not_not]; exact fun c _ ↦ c;
      · rfl;
      · apply omega_add_one_eqv_omega; intro h3; exact belong_to_self (ord_lt_le_trans h3 h);
    unfold succ; unfold succ_set; simp only; rw [←binary_union_assoc]; congr;
  rw [set_sub_union, binary_union_comm, ←subseteq_iff_eq_union]; exact h;

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

theorem card_sub {a b : set} (h : |b|.val s≅ b) (ha : a s⊆ b) : |a| ≤ |b| := by
  rcases h with ⟨f, h⟩; have h1 : f⁻¹[a] s⊆ |b|.val;
  · intro x hx; simp only [has_function.proof_range, pair_in_restrict, pair_in_inverse] at hx;
    rcases hx with ⟨y, hx1, hx2⟩; rw [h.1.2]; exact (has_function.proof_domain _).2 ⟨_, hx1⟩;
  have h1 := subseteq_trans h1 (On_is_ordinal_class.1 |b|.val |b|.prop);
  have h2 := ord_isom_we_set (E_well_order_ord_class h1);
  rcases h2 with ⟨α, ⟨g, h2⟩, _⟩; have hg := isom_set_eqv h2;
  have h3 := (card_def1 ⟨α, hg⟩).2 α hg;
  have hf1 : equiv _ _ := ⟨_, eqv_image (inv_one_one_onto h) ha⟩;
  have ha2 := eqv_trans hf1 (eqv_symm hg); have ha3 := eqv_ord_le ha2;
  apply ord_le_trans ha3; intro γ hg;
  let γ : ordinal := ⟨γ, ord_element_ord _ _ hg⟩;
  have h4 := monotone_ge_value (ord_isom_monotone h2 α.prop h1) γ
  conv at h4 => lhs; rw [←h2.1.1.2];
  have h4 := h4 hg; suffices hg2 : γ < |b|; · assumption;
  apply ord_le_lt_trans h4; suffices hg3 : g[[γ.val]] ∈ |b|.val; · assumption;
  rw [h.1.2, ←range_inv]; apply @restrict_range _ _ _ _ _ _ _ a;
  rw [←h2.1.2, has_function.proof_range]; use γ.val;
  have hg : γ ∈ D(g); · rw [←h2.1.1.2]; exact hg;
  exact value_func2 h2.1.1.1.2.1 hg;

theorem ord_lt_card {α β : ordinal} : |α.val| < |β.val| ↔ α < |β.val| := by
  constructor <;> intro h;
  · rw [←ord_nle] at *; intro h1; apply h; rw [←card_card];
    apply card_sub ord_eqv_card; exact h1;
  exact ord_le_lt_trans ord_card_le h;

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
theorem omega_card : ω = |ω.val| := by
  cases ord_le.1 ord_card_le with
  | inr => symm; assumption;
  | inl h =>
    exfalso; have h1 := @ord_eqv_card ω; have h2 := ord_eqv_nat h (eqv_symm h1);
    rw [←h2] at h; exact belong_to_self h;

def hartogs_type_graph (a : set) : Class := fun c ↦
  ∃ r x β : set, c = s⟨s⟨r, x⟩, β⟩ ∧ x s⊆ a ∧ is_well_order r x ∧
    r s⊆ a² ∧ ∃ _hβ : Ord(β), ∃ f : set, Isom f E r β x
theorem hartogs_type_graph_function {a : set} : Fnc(hartogs_type_graph a) := by
  constructor
  · intro c hc
    unfold hartogs_type_graph at hc
    rw [proof_in_Class] at hc
    rcases hc with ⟨r, x, β, hc, _⟩
    rw [hc, pair_in_product]
    exact ⟨set_in_allset, set_in_allset⟩
  intro u v w hvw
  rcases hvw with ⟨hv, hw⟩
  unfold hartogs_type_graph at hv hw
  rw [proof_in_Class] at hv hw
  rcases hv with ⟨rv, xv, βv, hv0, hxv, hrv, _, hβv, fv, hfv⟩
  rcases hw with ⟨rw, xw, βw, hw0, hxw, hrw, _, hβw, fw, hfw⟩
  rw [ordered_pair_eq_iff] at hv0
  rw [ordered_pair_eq_iff] at hw0
  rcases hv0 with ⟨huv, hvβ⟩
  rcases hw0 with ⟨huw, hwβ⟩
  rw [huv] at huw
  rw [ordered_pair_eq_iff] at huw
  rcases huw with ⟨hrw_eq, hxw_eq⟩
  subst rv
  subst xv
  subst βv
  subst βw
  have huniq := ord_isom_we_set hrv
  rcases huniq with ⟨δ, hδ, huniq⟩
  have hβ : (⟨v, hβv⟩ : ordinal) = δ := huniq ⟨v, hβv⟩ ⟨fv, hfv⟩
  have hγ : (⟨w, hβw⟩ : ordinal) = δ := huniq ⟨w, hβw⟩ ⟨fw, hfw⟩
  exact congrArg Subtype.val (Eq.trans hβ hγ.symm)
theorem hartogs_type_graph_domain_is_set {a : set} :
  D(hartogs_type_graph a).is_set := by
  apply subseteq_is_set (a := P(a²) × P(a))
  intro p hp
  rw [has_function.proof_domain] at hp
  rcases hp with ⟨β, hp⟩
  unfold hartogs_type_graph at hp
  rw [proof_in_Class] at hp
  rcases hp with ⟨r, x, γ, hp0, hx, _, hr, _⟩
  rw [ordered_pair_eq_iff] at hp0
  rcases hp0 with ⟨hp0, _⟩
  rw [hp0, pair_in_product]
  constructor
  · rw [axiom_of_power]
    exact hr
  rw [axiom_of_power]
  exact hx
theorem hartogs_type_graph_is_set {a : set} :
  (hartogs_type_graph a).is_set :=
  domain_is_set hartogs_type_graph_function hartogs_type_graph_domain_is_set
theorem hartogs_type_range_is_set {a : set} :
  W(hartogs_type_graph a).is_set :=
  @class_is_set_range _ hartogs_type_graph_is_set
theorem hartogs_type_range_subset_On {a : set} :
  W(hartogs_type_graph a) s⊆ On := by
  intro β hβ
  rw [has_function.proof_range] at hβ
  rcases hβ with ⟨p, hβ⟩
  unfold hartogs_type_graph at hβ
  rw [proof_in_Class] at hβ
  rcases hβ with ⟨r, x, γ, hβ0, _, _, _, hγ, _⟩
  rw [ordered_pair_eq_iff] at hβ0
  rcases hβ0 with ⟨_, hβ0⟩
  rw [hβ0]
  exact hγ
noncomputable def hartogs_type_set (a : set) : set :=
  W(hartogs_type_graph a).to_set hartogs_type_range_is_set
theorem hartogs_type_set_subset_On {a : set} :
  hartogs_type_set a s⊆ On := by
  intro β hβ
  unfold hartogs_type_set at hβ
  rw [Class_to_set_ext] at hβ
  exact hartogs_type_range_subset_On _ hβ
noncomputable def hartogs_ordinal (a : set) : ordinal :=
  succ ⟨∪(hartogs_type_set a), ord_class_union_ordinal (hartogs_type_set a)
    hartogs_type_set_subset_On⟩
def injects (a b : set) : Prop := ∃ f : set, f f: a -1-1-> b
infix:80 " s≼ " => injects
theorem eqv_subset_injects {a b c : set} (h : a s≅ b) (hbc : b s⊆ c) :
  a s≼ c := by
  rcases h with ⟨f, hf⟩
  use f
  constructor
  · exact hf.1
  rw [hf.2]
  exact hbc
theorem E_ord_restrict_well_order {α : ordinal} :
  is_well_order ((α.val × α.val) ∩ E) α.val :=
  well_order_restrict (E_well_order_ord α)
theorem E_ord_restrict_iff {α : ordinal} {x y : set}
  (hx : x ∈ α.val) (hy : y ∈ α.val) :
  ((α.val × α.val) ∩ E)& x y ↔ E& x y := by
  simp only [intersection_def, pair_in_product, hx, hy, true_and]
theorem ordinal_injects_mem_hartogs_type {a : set} {α : ordinal}
  (h : α.val s≼ a) : α.val ∈ hartogs_type_set a := by
  rcases h with ⟨f, hf⟩
  let x : set := W(f)
  have hx : x s⊆ a := hf.2
  have hfonto : f f: α.val -1-1onto->x := ⟨hf.1, rfl⟩
  let R : set := (α.val × α.val) ∩ E
  let r : set := (((f⁻¹) ∘ R) ∘ f)
  have hwo : is_well_order r x := by
    unfold r R
    exact eqv_well_order hfonto E_ord_restrict_well_order
  have hrsub : r s⊆ a² := by
    intro c hc
    have hrel := congr_relation c hc
    rw [has_product.proof_product] at hrel
    rcases hrel with ⟨u, _, v, _, hrel⟩
    rw [hrel, pair_in_product]
    rw [hrel] at hc
    unfold r at hc
    rw [pair_in_congr] at hc
    rcases hc with ⟨z, hz1, hz2⟩
    rw [pair_in_congr] at hz1
    rcases hz1 with ⟨w, hw1, _⟩
    rw [pair_in_inverse] at hw1
    constructor
    · apply hx
      rw [has_function.proof_range]
      exact ⟨w, hw1⟩
    apply hx
    rw [has_function.proof_range]
    exact ⟨z, hz2⟩
  unfold hartogs_type_set
  rw [Class_to_set_ext]
  rw [has_function.proof_range]
  use s⟨r, x⟩
  unfold hartogs_type_graph
  rw [proof_in_Class]
  use r
  use x
  use α.val
  constructor
  · rfl
  constructor
  · exact hx
  constructor
  · exact hwo
  constructor
  · exact hrsub
  use α.prop
  use f
  unfold r R
  have hi := eqv_isom (r := (α.val × α.val) ∩ E) hfonto
  rcases hi with ⟨hi1, hi2⟩
  constructor
  · exact hi1
  intro u hu v hv
  rw [←E_ord_restrict_iff hu hv]
  exact hi2 u hu v hv
theorem hartogs_ordinal_not_injects {a : set} :
  ¬((hartogs_ordinal a).val s≼ a) := by
  intro h
  have hmem := ordinal_injects_mem_hartogs_type h
  let U : set := ∪(hartogs_type_set a)
  have hU : U ∈ ∪(hartogs_type_set a) := by
    unfold make_union_reloaded
    rw [has_union.proof_union]
    use (hartogs_ordinal a).val
    constructor
    · unfold hartogs_ordinal
      change U ∈ (succ ⟨∪(hartogs_type_set a),
        ord_class_union_ordinal (hartogs_type_set a) hartogs_type_set_subset_On⟩).val
      exact self_belong_succ
    exact hmem
  exact belong_to_self hU

def finite (a : set) := ∃ n o∈ ω, a s≅ n.val
def infinite (a : set) := ¬(finite a)

theorem nat_finite {n : nat} : finite n.val.val := ⟨n.val, n.prop, eqv_refl⟩
theorem lt_omega_finite (h : n < ω) : finite n.val := ⟨_, h, eqv_refl⟩
theorem ord_infinite {α : ordinal} (h : ω ≤ α) : infinite α.val := by
  intro ⟨n, h1, h2⟩; have h3 := ord_eqv_nat h1 h2; subst α;
  exact belong_to_self (ord_le_lt_trans h h1);
theorem ord_infinite_iff {α : ordinal} : infinite α.val ↔ ω ≤ α := by
  constructor <;> intro h;
  · by_contra h1; apply h; rw [ord_nle] at h1; exact lt_omega_finite h1;
  exact ord_infinite h;

def is_card (α) := ∃ x, α = |x|
def card_class : Class := fun s ↦ ∃ h : Ord(s), is_card ⟨s, h⟩
def cardinal := {α : ordinal // is_card α}
def inf_card := {α : ordinal // is_card α ∧ infinite α.val}
def inf_card.to_card : inf_card → cardinal := fun c ↦ ⟨c.val, c.prop.1⟩
@[reducible] instance inf_card.coe_card : Coe inf_card cardinal := ⟨ inf_card.to_card ⟩
def cardinal.to_inf_card {κ : cardinal} (h : ω ≤ κ.val) : inf_card :=
  ⟨κ.val, ⟨κ.prop, ord_infinite h⟩⟩
theorem to_card_val_eq {α : inf_card} : α.to_card.val = α.val := rfl
theorem to_inf_card_val_eq {α : cardinal} {h : ω ≤ α.val} : (α.to_inf_card h).val = α.val := rfl

theorem cardinal_card {α : ordinal} : is_card α ↔ α = |α.val| := by
  constructor <;> intro h; swap; · use α.val;
  rcases h with ⟨x, h⟩; cases card_def_or x with
  | inl h1 => rw [h1] at h; subst α; symm; exact card_0;
  | inr h1 =>
    have h2 := @ord_eqv_card α; rw [←h] at h1; have h3 := eqv_trans h2 h1;
    have h4 := eqv_card_eq h3; rw [card_card, ←h] at h4; symm; exact h4;
theorem omega_sub_card {α : ordinal} (h : α < ω) : is_card α :=
  cardinal_card.2 (nat_card h)
theorem omega_is_card : is_card ω := cardinal_card.2 omega_card

instance cardinal.to_has_lt : LT cardinal := ⟨ fun a b ↦ a.val < b.val ⟩
instance cardinal.to_has_le : LE cardinal := ⟨ fun a b ↦ a.val ≤ b.val ⟩
instance inf_card.to_has_lt : LT inf_card := ⟨ fun a b ↦ a.val < b.val ⟩
instance inf_card.to_has_le : LE inf_card := ⟨ fun a b ↦ a.val ≤ b.val ⟩

theorem card_class_proper_class : Class.is_proper card_class := by
  intro hset
  let a : set := card_class.to_set hset
  have haOn : a s⊆ On := by
    intro x hx
    unfold a at hx
    rw [Class_to_set_ext] at hx
    rcases hx with ⟨hxOrd, _⟩
    exact hxOrd
  let α : ordinal := ⟨∪(a), ord_class_union_ordinal a haOn⟩
  let H : ordinal := hartogs_ordinal α.val
  let κ : ordinal := |H.val|
  have hκcard : κ.val ∈ card_class := by
    unfold card_class
    rw [proof_in_Class]
    use κ.prop
    unfold is_card
    use H.val
    unfold κ
    exact Subtype.ext rfl
  have hκa : κ.val ∈ a := by
    unfold a
    rw [Class_to_set_ext]
    exact hκcard
  have hκsub : κ.val s⊆ α.val := by
    unfold α
    exact unionset_subseteq hκa
  have hHinj : H.val s≼ α.val :=
    eqv_subset_injects (eqv_symm (ord_eqv_card (α := H))) hκsub
  exact hartogs_ordinal_not_injects hHinj

theorem exists_Aleph : ∃ F : Class, Isom F E E On (card_class - ω.val) := by
  let G : Class := fun c ↦ ∃ x y, c = s⟨x, y⟩ ∧
    y ∈ (card_class - ω.val) - W(x) ∧
    ((card_class - ω.val) - W(x)) ∩ E⁻¹[s{y}] = s0
  use trans_rec_class G
  have hc : Class.is_proper (card_class - ω.val);
  · intro hset
    let a : set := (card_class - ω.val).to_set hset
    have hsub : card_class s⊆ a ∪ ω.val := by
      intro x hx
      by_cases hxω : x ∈ ω.val
      · rw [binary_union_def]
        right
        exact hxω
      rw [binary_union_def]
      left
      unfold a
      rw [Class_to_set_ext]
      rw [class_sub_is_sub]
      exact ⟨hx, hxω⟩
    exact card_class_proper_class (subseteq_is_set hsub)
  have hc2 : (card_class - ω.val) s⊆ On
  · intro x hx
    rw [class_sub_is_sub] at hx
    rcases hx.1 with ⟨hxOrd, _⟩
    exact hxOrd
  exact ord_isom_ord_class hc hc2 rfl
noncomputable def Aleph : Class := Classical.choose exists_Aleph
theorem Aleph_spec : Isom Aleph E E On (card_class - ω.val) :=
  Classical.choose_spec exists_Aleph
theorem aleph_is_ord (α : ordinal) : ∃ h : Ord(Aleph[[α.val]]), is_card ⟨Aleph[[α.val]], h⟩ := by
  rcases Aleph_spec with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩;
  have ha : α ∈ On := α.prop; rw [h2] at ha; have ha2 := value_func2 h1.2.1 ha;
  have h5 := (has_function.proof_range _).2 ⟨_, ha2⟩; rw [h3] at h5;
  exact h5.1;
theorem aleph_infinite (α : ordinal) : infinite (Aleph[[α.val]]) := by
  intro ⟨n, h1, h2⟩; have h0 : α ∈ D(Aleph); · rw [←Aleph_spec.1.1.2]; exact α.prop;
  have h3 := (has_function.proof_range _).2 ⟨_, value_func2 Aleph_spec.1.1.1.2.1 h0⟩;
  rw [Aleph_spec.1.2, class_sub_is_sub] at h3;
  have h4 := aleph_is_ord α; let o : ordinal := ⟨_, h4.fst⟩;
  have h5 := @ord_eqv_nat o _ h1 h2; have h6 : o.val ∉ ω := h3.2; rw [h5] at h6; exact h6 h1;

noncomputable def aleph (α : ordinal) : inf_card := ⟨⟨Aleph[[α.val]],
  (aleph_is_ord α).fst⟩, ⟨(aleph_is_ord α).snd, aleph_infinite α⟩⟩
notation "ℵ_(" α ")" => aleph α
theorem aleph_ord_lt {α β : ordinal} : α < β ↔ ℵ_(α).val < ℵ_(β).val := by
  suffices h1 : ∀ {α β}, α < β → ℵ_(α).val < ℵ_(β).val;
  · use h1; intro h2; cases @ord_total α β with
    | inl => assumption;
    | inr h3 => exfalso; cases h3 with
      | inl => subst α; exact belong_to_self h2;
      | inr h3 => exact belong_to_2 h2 (h1 h3)
  intro α β h; have h2 := (Aleph_spec.2 α.val α.prop β.val β.prop).1; simp only [E_simp] at h2;
  exact h2 h;
theorem aleph_ord_le {α β : ordinal} : α ≤ β ↔ ℵ_(α).val ≤ ℵ_(β).val := by
  have h := @aleph_ord_lt β α;
  rw [←ord_nle] at h; conv at h => rhs; rw [←ord_nle];
  simp only [iff_not_comm, not_not] at h; symm; assumption;
theorem aleph_ext {α β : ordinal} : ℵ_(α) = ℵ_(β) ↔ α = β := by
  constructor <;> intro h; swap; · subst α; rfl;
  cases' ord_total with h1 h1; swap; cases' h1 with h1 h1; · exact h1;
  all_goals have h1 := aleph_ord_lt.1 h1; rw [h] at h1; exfalso; exact belong_to_self h1;
theorem aleph_range {α : ordinal} : ω ≤ ℵ_(α).val := by
  have h1 : ℵ_(α).val.val ∈ W(Aleph);
  · rw [has_function.proof_range]; use α.val; have ha : α ∈ D(Aleph);
    · rw [←Aleph_spec.1.1.2]; exact α.prop
    exact value_func2 Aleph_spec.1.1.1.2.1 ha;
  rw [Aleph_spec.1.2] at h1; intro n hn; let n : ordinal := ⟨n, ord_element_ord _ _ hn⟩;
  cases @ord_total n ℵ_(α).val with
  | inl => assumption;
  | inr h3 => exfalso; cases h3 with
    | inl h3 => rw [←h3] at h1; have h1 := h1.2; exact h1 hn;
    | inr h3 =>
      have h4 := ω.prop.1 _ hn _ h3; exact h1.2 h4;
theorem aleph_value_exists (κ : inf_card) : ∃ α, κ = ℵ_(α) := by
  have h1 : κ.val.val ∈ card_class - ω.val;
  · use ⟨κ.val.prop, κ.prop.1⟩; simp only [←set_belong_set_to_class]; intro h1;
    have h1 := ord_le_lt_trans (ord_infinite_iff.1 κ.prop.2) h1; exact belong_to_self h1;
  rw [←Aleph_spec.1.2, has_function.proof_range] at h1; rcases h1 with ⟨x, h1⟩;
  have h2 := (has_function.proof_domain _).2 ⟨_, h1⟩;
  rw [←Aleph_spec.1.1.2] at h2; let x : ordinal := ⟨x, h2⟩; use x;
  have h3 := value_func Aleph_spec.1.1.1.2.1 h1;
  apply Subtype.ext; apply Subtype.ext; symm; exact h3;

theorem aleph_0_eq_omega : ℵ_(o0).val = ω := by
  apply ord_le_antisymm; swap; · exact aleph_range;
  -- have h5 := @aleph_ord o0;
  let h1 : inf_card := ⟨ω, omega_is_card, by rw [ord_infinite_iff]⟩; have h2 : ω = h1.val := rfl;
  have h3 := aleph_value_exists h1;
  rcases h3 with ⟨α, h3⟩; have h4 := aleph_ord_le.1 (@ord_ge_0 α);
  rw [←h3] at h4; assumption;
theorem sup_card_is_card {a : set} (h : a s⊆ card_class) : ∃ h : Ord(∪(a)), is_card ⟨∪(a), h⟩ := by
  have h1 : a s⊆ On; · intro x hx; exact (h x hx).fst;
  have h1 := ord_class_union_ordinal a h1; use h1; let ua : ordinal := ⟨∪(a), h1⟩;
  use ∪(a); apply ord_le_antisymm; swap; · exact @ord_card_le ua;
  by_contra h2; rw [ord_nle] at h2; have h3' : |ua.val|.val ∈ ∪(a) := h2;
  have h3 := has_union.proof_union.1 h3'; rcases h3 with ⟨c, h3, h4⟩;
  let κ : cardinal := ⟨⟨c, (h _ h4).fst⟩, (h _ h4).snd⟩;
  rcases eqv_symm (@ord_eqv_card ua) with ⟨f, h5, h6⟩; have h7 := unionset_subseteq h4;
  have h9 : f[c] s⊆ |ua.val|.val; · rw [←h6]; exact restrict_range;
  have h10 := card_sub ord_eqv_card h9; rw [card_card] at h10;
  have h11 := eqv_card_eq ⟨_, eqv_image ⟨h5, h6⟩ h7⟩; rw [←h11] at h10;
  have h12 : κ.val = |c| := cardinal_card.1 κ.prop; rw [←h12] at h10;
  have h9 : |ua.val| < κ.val := h3; exact belong_to_self (ord_le_lt_trans h10 h9);

theorem aleph_continue {α : ordinal} (h : α.val ∈ K2) : ⋃(γ oo∈ α, ℵ_(γ).val) = ℵ_(α).val := by
  apply Subtype.ext; rw [←ordinal_union_axiom];
  have h1 : ordinal_replacement α fun γ _y ↦ _y = ℵ_(γ).val.val s⊆ card_class;
  · intro x hx; rw [mem_ordinal_replacement] at hx;
    rcases hx with ⟨y, hx1, hx2⟩; subst x; exact ⟨ℵ_(y).val.prop, ℵ_(y).prop.1⟩;
  rcases sup_card_is_card h1 with ⟨he1, he2⟩;
  let s : cardinal := ⟨⟨∪(ordinal_replacement α fun γ _y ↦ _y = ℵ_(γ).val.val), he1⟩, he2⟩;
  suffices hs : s = ℵ_(α).to_card; · exact Subtype.coe_inj.2 (Subtype.coe_inj.2 hs);
  have hs : s.val = ⋃(γ oo∈ α, ℵ_(γ).val); · apply Subtype.ext; rw [←ordinal_union_axiom];
  have h2 : ω ≤ s.val;
  · have ha := ord_k2_gt_0 h; rw [hs, ←aleph_0_eq_omega];
    exact @ord_union_le_sup α (fun a ↦ ℵ_(a).val) o0 ha;
  rcases aleph_value_exists (s.to_inf_card h2) with ⟨β, he⟩;
  have he : s.val = ℵ_(β).val := Subtype.coe_inj.2 he; rw [he] at hs;
  apply Subtype.ext; rw [he]; apply ord_le_antisymm;
  · rw [hs]; apply ord_union_sup_le; intro γ h3; apply ord_lt_le; exact aleph_ord_lt.1 h3;
  rw [to_card_val_eq, ←aleph_ord_le]; intro γ hg; let γ : ordinal := ⟨γ, ord_element_ord _ _ hg⟩;
  have hg : γ < α := hg; convert_to γ < β; · rfl;
  rw [aleph_ord_lt, hs]; have hg2 := @ord_union_le_sup α (fun a ↦ ℵ_(a).val) _ hg;
  rw [ord_le] at hg2; cases hg2 with
  | inl => assumption;
  | inr hg3 =>
    exfalso; have hg1 := ord_k2_succ_in h hg;
    have hg4 := @ord_union_le_sup α (fun a ↦ ℵ_(a).val) _ hg1; rw [←hg3] at hg4;
    rw [←aleph_ord_le] at hg4; exact belong_to_self (ord_le_lt_trans hg4 ord_lt_succ);
theorem aleph_smo : strict_monotone Aleph := by
  constructor;
  · use ⟨Aleph_spec.1.1.1.1, Aleph_spec.1.1.1.2.1⟩;
    rw [←Aleph_spec.1.1.2, Aleph_spec.1.2]; use On_is_ordinal_class; intro x hx;
    rw [class_sub_is_sub] at hx; exact hx.1.1;
  intro α h1 β h2 h3; exact aleph_ord_lt.1 h3;

def cof (α β : ordinal) := β ≤ α ∧ ∃ f : set, ∃ h : strict_monotone f, (f f: β.val -Fnc-> α.val) ∧
  ∀ γ o∈ α, ∃ δ, ∃ hd : δ ∈ D(f), γ ≤ ord_func_value h.1 hd
@[refl] theorem cof_refl {α} : cof α α := by
  constructor; · rfl;
  let rx := @restrict_is_set I α.val ⟨id_one_one.1, id_one_one.2.1⟩;
  use (I Γ α.val).to_set rx;
  use (@monotone_to_set _ rx).2 (I_monotone α.prop); constructor; constructor;
  · unfold Fnc_on; simp only [class_to_set_func, class_to_set_domain];
    use restrict_is_func ⟨id_one_one.1, id_one_one.2.1⟩;
    rw [←extensionality_belong]; intro x;
    simp [Class_to_set_ext, domain_restrict];
  · intro x; simp [class_to_set_range, set_to_Class_to_set_has_belong];
  intro β h; unfold ord_func_value; use β;
  simp only [class_to_set_value, class_to_set_domain, domain_restrict, id_domain, inter_V,
    ord_belonged_to, Class_to_set_ext, set_belong_to_class2]; use h; rw [ord_le]; right;
  conv => rhs; lhs; rw [restrict_value (ord_belong.1 h)]; simp only [id_value];
  rfl;
@[trans] theorem cof_trans {α β γ} : cof α β → cof β γ → cof α γ := by
  intro ha hb; use ord_le_trans hb.1 ha.1;
  rcases ha.2 with ⟨f1, ha1, ⟨ha2, ha3⟩, ha4⟩;
  rcases hb.2 with ⟨f2, hb1, ⟨hb2, hb3⟩, hb4⟩; use f2 ∘ f1;
  use strict_monotone_congr hb1 ha1; constructor; constructor;
  · use ⟨congr_relation, congr_unitary hb2.1.2 ha2.1.2⟩;
    rw [hb2.2]; symm; apply congr_domain3; rwa [←ha2.2];
  · exact subseteq_trans congr_range ha3;
  intro δ hd; rcases ha4 _ hd with ⟨δ1, hd1, hd2⟩; have hd1' := hd1;
  rw [←ha2.2] at hd1'; rcases hb4 _ hd1' with ⟨δ2, hd3, hd4⟩; use δ2;
  have hd3' := hd3; rw [←congr_domain3] at hd3;
  · use hd3; apply ord_le_trans hd2;
    have hd5 := fun x ↦ strict_monotone_value_le ha1 _ hd1 _ x hd4;
    have hd5 : (_ : ordinal) ≤ _;
    · apply hd5; rw [ord_belonged_to]; convert_to f2[[δ2.val]] ∈ D(f1); · rfl;
      rw [←ha2.2]; apply hb3; rw [has_function.proof_range]; use δ2.val;
      exact value_func2 hb1.1.1.2 hd3';
    suffices hd6 : ord_func_value _ hd3 = _; · rewrite [hd6]; exact hd5;
    symm; apply Subtype.ext;
    have hx : ∀ {α} [has_belong α] [has_intersection α Class] [has_value α]
      (G : α) {h} {α} {ha}, (@ord_func_value _ _ _ _ G h α ha).val = G[[α.val]] :=
      fun _ _ _ _ ↦ rfl;
    rw [hx, hx, hx]; symm; apply congr_value hb1.1.1.2 ha1.1.1.2 hd3';
    exact congr_domain2 hb1.1.1.2 hd3;
  rwa [←ha2.2];

theorem cof_0 {α : ordinal} : cof α o0 ↔ α = o0 := by
  constructor <;> intro h; swap; · subst α; rfl;
  rcases h with ⟨_, f, h1, ⟨h2, h3⟩, h4⟩;
  have h5 := domain_empty_set h2; subst f;
  have h4 : ∀ γ, γ ∈ α → ∃ δ, δ ∈ D(s0) := fun a b ↦ (fun ⟨c, d, e⟩ ↦ ⟨c, d⟩) (h4 a b);
  simp only [ord_belonged_to, has_function.proof_domain, empty_false, exists_false,
    imp_false] at h4;
  apply Subtype.ext; rw [←extensionality_belong]; intro a;
  simp only [o0_eq_s0, empty_false, iff_false];
  intro ha; exact h4 ⟨a, ord_element_ord _ _ ha⟩ ha;
theorem cof_k1 {α β : ordinal} : α ∈ K1 → β ∈ K1 → o0 < β → β ≤ α → cof α β := by
  intro h1 h2 h3 h4; have h5 := ord_lt_le_trans h3 h4;
  have h1 := k1 h1; have h2 := k1 h2; rw [←ord_ne_0_gt_iff] at h3 h5;
  rw [or_iff_not_imp_left] at h1 h2;
  rcases h1 h5 with ⟨γ, h5⟩; rcases h2 h3 with ⟨δ, h3⟩; subst α β;
  use h4; use ((I Γ δ).to_set (restrict_is_set id_fnc)) ∪ s{s⟨δ.val, γ.val⟩};
  have hh : has_belong.to_Class δ = δ.val.to_Class := rfl;
  suffices ha : _; suffices hb : _; suffices hc : _; suffices hd : _; suffices he : _;
  constructor; constructor; constructor; constructor;
  · exact hb;
  · exact ha;
  · exact hc;
  · intro α hax; have hax := ord_lt_succ_iff.1 hax;
    use δ; have hdx : δ ∈ (succ δ).val := ord_lt_succ; rw [ha] at hdx;
    use hdx; intro x hx; rw [set_ord_belong];
    convert_to x ∈ ((I Γ δ).to_set _ ∪ s{s⟨δ.val, γ.val⟩})[[_]]; · rfl;
    rw [binary_union_comm, union_function_apply_set function_one_pair.1
      hd he, value_one_pair];
    · exact hax _ hx;
    simp only [←function_one_pair.2, element_in_one_element_set];
  swap;
  · rw [←function_one_pair.2, class_to_set_domain, intersection_right_to_set];
    simp only [domain_restrict, id_domain, inter_V, hh];
    rw [←extensionality_belong]; intro a; simp only [intersection_def,
      element_in_one_element_set, ← set_belong_set_to_class, empty_false, iff_false, not_and];
    intro; subst a; exact belong_to_self;
  swap; · exact (class_to_set_func.2 (restrict_is_func id_fnc));
  swap;
  · rw [range_union, range_one_pair, class_to_set_range];
    simp only [id_range2, hh, set_to_Class_to_set, union_subseteq_iff];
    use ord_lt_le (ord_lt_le_trans ord_lt_succ h4); intro x;
    simp only [element_in_one_element_set]; intro _; subst x;
    exact ord_lt_succ;
  swap;
  · apply union_function; · rw [class_to_set_func]; exact restrict_is_func id_fnc;
    · exact function_one_pair.1;
    have hh : ∀ s : set, has_belong.to_Class s = s.to_Class := fun _ ↦ rfl; rw [hh];
    rw [class_to_set_domain, ←function_one_pair.2, ←intersection_left_set,
      Class_to_set_to_Class, ←extensionality_belong]; intro a;
    simp only [domain_restrict, id_domain, inter_V, intersection_def, set_belong_to_class2,
      element_in_one_element_set, ←set_belong_set_to_class, empty_false, iff_false, not_and];
    intro ha1 ha2; subst a; exact belong_to_self ha1;
  swap;
  · rw [domain_union, ←function_one_pair.2, class_to_set_domain];
    conv => rhs; lhs; lhs; simp only [domain_restrict, id_domain, inter_V, hh];
    rw [set_to_Class_to_set]; rfl;
  constructor; constructor; · assumption;
  constructor; · rw [←ha]; exact (succ δ).prop;
  · apply subseteq_trans hc; intro x; exact ord_element_ord _ _;
  intro α a1 β a2 a3; rw [←ha] at a1 a2;
  have a1 : α < succ δ := a1; have a2' : β < succ δ := a2;
  rw [ord_lt_succ_iff, ord_le] at a1 a2';
  have he' := he; rw [intersection_comm] at he';
  have hf1 := union_function_apply_set hd function_one_pair.1 he';
  simp only [class_to_set_value] at hf1;
  have hf2 := union_function_apply_set function_one_pair.1 hd he;
  rw [binary_union_comm] at hf2; have h5 := ord_succ_le_succ_iff.2 h4;
  cases a1 with
  | inl a1 => cases a2' with
    | inl a2 =>
      rw [hf1, hf1];
      · simp only [restrict_value a1, id_value, restrict_value a2]; exact a3;
      all_goals simp only [class_to_set_domain, domain_restrict, id_domain, inter_V,
        Class_to_set_ext, set_belong_to_class2]; assumption;
    | inr a2 =>
      subst β; rw [hf1, hf2];
      · rw [restrict_value a1, value_one_pair]; simp only [id_value];
        exact ord_lt_le_trans a1 h5;
      · simp only [←function_one_pair.2, element_in_one_element_set];
      · simp only [class_to_set_domain, domain_restrict, id_domain, inter_V, Class_to_set_ext,
        set_belong_to_class2]; exact a1;
  | inr a1 => subst α; exfalso; exact ord_no_between_succ ⟨a3, a2⟩;
theorem cof_k2 {α β} (h : cof α β) : α.val ∈ K2 ↔ β.val ∈ K2 := by
  rcases h with ⟨h1, f, h, ⟨h2, h3⟩, h4⟩; constructor <;> intro h5; swap;
  · cases k12 α with
    | inr => assumption;
    | inl h6 => exfalso; cases h6 with
      | inl => subst α; have h1 := ord_le_antisymm ord_ge_0 h1; subst β;
                exact belong_to_self (ord_k2_gt_0 h5);
      | inr h6 =>
        rcases h6 with ⟨γ, _⟩; subst α; rcases h4 _ ord_lt_succ with ⟨δ, hd, h4⟩;
        suffices hb : β = succ δ; · exact (ord_in_k2.1 h5).2 ⟨_, hb⟩;
        have a1 := fun a b c ↦ ord_le_lt_trans h4 (strict_monotone_value h δ hd a b c);
        conv at a1 => rhs; rhs; rw [←ord_nle, ←ord_nle, not_imp_not]; lhs; rw [←ord_lt_succ_iff]
        have a2 : ∀ a o∈ D(f), f[[a.val]] ∈ (succ γ).val;
        · intro a ha; exact h3 _ ((has_function.proof_range _).2 ⟨_, value_func2 h.1.1.2 ha⟩);
        have a3 := fun a b ↦ a1 a b (a2 a b); rw [←h2.2] at a3;
        conv at a3 => rhs; rw [←ord_lt_succ_iff];
        apply ord_le_antisymm; · intro a h; exact a3 ⟨a, ord_element_ord _ _ h⟩ h;
        rw [←h2.2] at hd; exact ord_succ_belong_le hd;
  cases k12 β with
  | inr => assumption;
  | inl h6 => exfalso; cases h6 with
    | inl => subst β; have h6 := cof_0.1 ⟨h1, f, h, ⟨h2, h3⟩, h4⟩; subst α;
              exact belong_to_self (ord_k2_gt_0 h5);
    | inr h6 =>
      rcases h6 with ⟨γ, _⟩; subst β; rw [←ord_succ_belong_le_iff] at h1;
      have h7 : γ ∈ (succ γ).val := @ord_lt_succ γ; rw [h2.2] at h7;
      have a1 := h4 (succ (ord_func_value h.1 h7));
      have a2 : f[[γ.val]] ∈ α;
      · apply h3; exact (has_function.proof_range _).2 ⟨_, value_func2 h.1.1.2 h7⟩;
      have a2 : ord_func_value h.1 h7 ∈ α := a2; have a2 := ord_k2_succ_in h5 a2;
      rcases a1 a2 with ⟨δ, hd, a3⟩; rw [←ord_succ_belong_le_iff] at a3;
      have hd' := hd; rw [←h2.2] at hd'; have hd' := ord_lt_succ_iff.1 hd';
      have a4 := strict_monotone_value_le h δ hd γ h7 hd';
      exact belong_to_self (ord_le_lt_trans a4 a3);

theorem cf_lt {α β : ordinal} (h1 : β < α) : (∃ f, ∃ hf : f f: β.val -Fnc-> α.val,
  ∀ γ o∈ α, ∃ δ, ∃ hd : δ ∈ D(f), γ ≤ ord_func_value ⟨hf.1.1, by {
    rw [←hf.1.2]; exact β.prop;}, subseteq_trans hf.2 (ord_element_ord _)⟩
  hd) → ∃ η, η ≤ β ∧ cof α η := by
  intro ⟨f, ⟨h2, h3⟩, h4⟩; have hf : ord_func f := ⟨h2.1, by {
    rw [←h2.2]; exact β.prop;}, subseteq_trans h3 (ord_element_ord _)⟩;
  let A : Class := fun b ↦ ∀ γ o∈ b, f[[γ.val]] ∈ f[[b]]; let a : set := β.val ∩ A;
  have a1 : a s⊆ β.val := intersection_subseteq_left;
  rcases ord_isom_we_set (E_well_order_ord_class (subseteq_trans a1 (ord_element_ord _)))
    with ⟨η, ⟨h, h5⟩, _⟩;
  have m1 := ord_isom_monotone h5 η.prop (subseteq_trans a1 (ord_element_ord _));
  use η; suffices hn : _; use hn; swap;
  · have m2 := monotone_ge_value m1; intro x hx; simp only [←h5.1.1.2] at m2;
    have m3 := m2 ⟨x, ord_element_ord _ _ hx⟩ hx;
    refine ord_le_lt_trans m3 ?_; apply a1; convert_to h[[x]] ∈ a; · rfl;
    rw [←h5.1.2]; refine (has_function.proof_range _).2 ⟨_, value_func2 h5.1.1.1.2.1 ?_⟩;
    rwa [←h5.1.1.2];
  have n1 : D(h ∘ f) = D(h); · rw [congr_domain3]; rwa [h5.1.2, ←h2.2];
  have n2 : D(h ∘ f) = η.val; · rw [n1, ←h5.1.1.2];
  use ord_lt_le (ord_le_lt_trans hn h1); use h ∘ f; suffices f1 : _; use f1; swap;
  · constructor;
    · use ⟨congr_relation, congr_unitary h5.1.1.1.2.1 hf.1.2⟩; rw [n2];
      use η.prop; exact subseteq_trans congr_range (subseteq_trans h3 (ord_element_ord _));
    intro δ d1 γ d2 d3; rw [n1] at d1 d2; have d4 : h[[γ.val]] ∈ a;
    · rw [←h5.1.2]; exact (has_function.proof_range _).2 ⟨_, value_func2 h5.1.1.1.2.1 d2⟩;
    have d5 : h[[δ.val]] ∈ a;
    · rw [←h5.1.2]; exact (has_function.proof_range _).2 ⟨_, value_func2 h5.1.1.1.2.1 d1⟩;
    rw [congr_value h5.1.1.1.2.1 hf.1.2, congr_value h5.1.1.1.2.1 hf.1.2]; assumption';
    · unfold a at d4; rw [intersection_def] at d4; have d4 := d4.2; rw [proof_in_Class] at d4;
      unfold A at d4;
      have d5 := a1 _ d5; have d5 := ord_element_ord _ _ d5;
      exact d4 ⟨_, d5⟩ (m1.2 _ d1 _ d2 d3);
    all_goals rw [←h2.2]; apply a1; assumption;
  constructor; constructor;
  · use ⟨congr_relation, congr_unitary h5.1.1.1.2.1 hf.1.2⟩; symm; assumption;
  · exact subseteq_trans congr_range h3;
  intro γ g1; have g2 := h4 _ g1; rcases minimal_ordinal g2 with ⟨δ, ⟨g3, g4⟩, g5⟩;
  have g6 : δ ∈ A;
  · rw [ord_belonged_to, proof_in_Class]; unfold A; intro ε e1;
    have e2 := g5 ε; rw [←not_imp_not, ord_nle] at e2; push Not at e2;
    have e2 := e2 e1; simp only [← h2.2] at e2 g3; have e2 := e2 (ord_lt_trans e1 g3);
    rw [ord_nle] at e2; exact ord_lt_le_trans e2 g4;
  have g6 : δ ∈ a; · unfold a; rw [ord_belonged_to, intersection_def, h2.2]; use g3; use g6;
  have g6' := g6;
  rw [←h5.1.2, ord_belonged_to, has_function.proof_range] at g6; rcases g6 with ⟨μ, g6⟩;
  have g7 := (has_function.proof_domain _).2 ⟨_, g6⟩; rw [←h5.1.1.2] at g7;
  let μ : ordinal := ⟨μ, ord_element_ord _ _ g7⟩; use μ;
  simp only [n2]; use g7; suffices g8 : ord_func_value _ g3 = _; · rw [g8] at g4; exact g4;
  apply Subtype.ext; convert_to f[[δ.val]] = (h ∘ f)[[μ.val]]; any_goals rfl;
  rw [congr_value h5.1.1.1.2.1 hf.1.2]; · congr 1; symm; exact value_func h5.1.1.1.2.1 g6;
  · rwa [←h5.1.1.2];
  rw [←h2.2]; apply a1; rwa [value_func h5.1.1.1.2.1 g6];
theorem cf_lt2 {α β : ordinal} (h1 : β ≤ α) (h2 : β.val s≅ α.val) : ∃ η, η ≤ β ∧ cof α η := by
  cases ord_le.1 h1 with
  | inl h1 =>
    apply cf_lt h1; rcases h2 with ⟨f, h2, h3⟩; use f; suffices h4 : _; use h4; swap;
    · use ⟨⟨h2.1.1, h2.1.2.1⟩, h2.2⟩; rw [h3];
    intro γ g1; have g2 : γ ∈ W(f); · rwa [h3];
    rw [ord_belonged_to, has_function.proof_range] at g2; rcases g2 with ⟨δ, g2⟩;
    have g3 := (has_function.proof_domain _).2 ⟨_, g2⟩; have g3' := g3;
    rw [←h2.2] at g3; let δ : ordinal := ⟨δ, ord_element_ord _ _ g3⟩;
    use δ; use g3'; suffices g4 : γ = _; · rw [g4];
    apply Subtype.ext; symm; exact value_func h2.1.2.1 g2;
  | inr => subst β; use α;

theorem cof_union {α β : ordinal} (h1 : α.val ∈ K2) (h2 : cof α β) :
  ∃ f, strict_monotone f ∧ Fnc_on f β.val ∧ α.val = ∪(W(f)) := by
  have hb := (cof_k2 h2).1 h1;
  rcases h2 with ⟨h2, f, h3, ⟨h4, h5⟩, h6⟩; use f; use h3; use h4;
  rw [←extensionality_belong]; intro x;
  unfold make_union_reloaded; rw [has_union.proof_union];
  constructor <;> intro h;
  · let x : ordinal := ⟨x, ord_element_ord _ _ h⟩; rcases h6 x h with ⟨γ, h7, h8⟩;
    have h7' := h7; rw [←h4.2] at h7'; have h7' : succ γ ∈ β.val := ord_k2_succ_in hb h7';
    rw [h4.2] at h7'; have h9 := strict_monotone_value h3 _ h7 _ h7' ord_lt_succ;
    have h9 := ord_le_lt_trans h8 h9; use (ord_func_value h3.1 h7').val; use h9;
    convert_to f[[(succ γ).val]] ∈ W(f); · rfl;
    exact (has_function.proof_range _).2 ⟨_, value_func2 h4.1.2 h7'⟩;
  rcases h with ⟨c, c1, c2⟩; have c3 := h5 _ c2; exact α.prop.1 _ c3 _ c1;
theorem cof_union2 {α β : ordinal} (h1 : β.val ∈ K2) :
  strict_monotone f → Fnc_on f β.val → α.val = ∪(W(f)) → cof α β := by
  intro h2 h3 h4; constructor;
  · intro x hx; let x : ordinal := ⟨x, ord_element_ord _ _ hx⟩;
    have h5 := monotone_ge_value h2 (succ x); simp only [← h3.2] at h5;
    have h5 := h5 (ord_k2_succ_in h1 hx); have h5 := ord_lt_le_trans ord_lt_succ h5;
    convert_to x.val ∈ α.val; · rfl;
    rw [h4, make_union_reloaded, has_union.proof_union];
    use f[[(succ x).val]]; use h5;
    refine (has_function.proof_range _).2 ⟨_, value_func2 h2.1.1.2 ?_⟩;
    rw [←h3.2]; exact ord_k2_succ_in h1 hx;
  · use f; use h2; constructor;
    · use h3; intro x hx; rw [has_function.proof_range] at hx; rcases hx with ⟨y, hx⟩;
      have dy := (has_function.proof_domain _).2 ⟨_, hx⟩; rw [←h3.2] at dy;
      let y : ordinal := ⟨y, ord_element_ord _ _ dy⟩;
      rw [h4, make_union_reloaded, has_union.proof_union];
      use f[[(succ y).val]]; have d1 := h2.2 y; simp only [←h3.2] at d1;
      have d1 := d1 dy (succ y) (ord_k2_succ_in h1 dy) ord_lt_succ;
      rw [value_func h2.1.1.2 hx] at d1; use d1;
      refine (has_function.proof_range _).2 ⟨_, value_func2 h2.1.1.2 ?_⟩;
      rw [←h3.2]; exact ord_k2_succ_in h1 dy;
    intro γ d1; rw [ord_belong, h4, make_union_reloaded, has_union.proof_union] at d1;
    rcases d1 with ⟨c, d1, d2⟩; rw [has_function.proof_range] at d2;
    rcases d2 with ⟨w, d2⟩;
    have dy := (has_function.proof_domain _).2 ⟨_, d2⟩; have dy' := dy;
    rw [←h3.2] at dy'; let w : ordinal := ⟨w, ord_element_ord _ _ dy'⟩;
    use w; use dy; apply ord_lt_le; rw [←value_func h2.1.1.2 d2] at d1; exact d1;

theorem cof_aleph {α} (h : α.val ∈ K2) : cof ℵ_(α).val α := by
  have ha : Fnc(Aleph) := ⟨Aleph_spec.1.1.1.1, Aleph_spec.1.1.1.2.1⟩;
  apply cof_union2 h; · exact (@monotone_to_set _ (restrict_is_set ha)).2
                          (restrict_monotone α.prop aleph_smo);
  constructor; · rw [class_to_set_func]; exact restrict_is_func ha;
  · rw [class_to_set_domain];
    conv => rhs; lhs; rw [domain_restrict, ←Aleph_spec.1.1.2];
    conv => lhs; rw [←@set_to_Class_to_set α.val (set_to_Class_is_set)];
    congr; rw [intersection_to_class, intersection_comm, ←subseteq_iff_eq_intersection];
    intro x hx; exact ord_element_ord _ _ hx;
  symm; rw [←aleph_continue h, ←extensionality_belong]; intro x;
  unfold ordinal_function_union make_union_reloaded;
  simp only [has_union.proof_union, has_function.proof_range, Class_to_set_ext, pair_in_restrict,
    and_imp, forall_eq_apply_imp_iff, imp_self, implies_true, mem_ordinal_replacement2,
    ↓existsAndEq, true_and, and_true]; constructor <;> intro h1;
  · rcases h1 with ⟨c, h1, y, h2, h3⟩; have h4 := (has_function.proof_domain _).2 ⟨_, h2⟩;
    rw [←Aleph_spec.1.1.2] at h4; let y : ordinal := ⟨y, h4⟩; use succ y;
    have h5 := value_func ha.2 h2; have h5 : ℵ_(y).val.val = c := h5;
    rw [←h5] at h1; use ord_lt_le (aleph_ord_lt.1 ord_lt_succ) x h1; exact ord_k2_succ_in h h3;
  rcases h1 with ⟨c, h1, h2⟩; use ℵ_(c).val.val; use h1; use c.val;
  have h3 : c ∈ D(Aleph); · rw [←Aleph_spec.1.1.2]; exact c.prop;
  use value_func2 ha.2 h3; exact h2;

noncomputable def cfo (α : ordinal) : ordinal := Classical.choose
  (@minimal_ordinal (fun β ↦ cof α β) ⟨_, cof_refl⟩)
theorem cfo_spec : cof α (cfo α) ∧ ∀ γ, cof α γ → cfo α ≤ γ :=
  Classical.choose_spec (minimal_ordinal ⟨_, cof_refl⟩)

def lim_ord := {α : ordinal // α ∈ K2}
theorem lim_ord_cf_inf {α : lim_ord} : infinite (cfo α.val).val := by
  rw [ord_infinite_iff]; apply ord_k2_ge_omega;
  rw [ord_belonged_to, ←cof_k2 cfo_spec.1]; exact α.prop;

theorem cf_is_card {α} : is_card (cfo α) := by
  rw [cardinal_card];
  suffices h : ∀ γ : ordinal, γ.val s≅ (cfo α).val → cfo α ≤ γ;
  · apply ord_le_antisymm; swap; · exact ord_card_le;
    apply h; exact ord_eqv_card;
  intro γ h1; by_contra h2; rw [ord_nle] at h2;
  rcases cf_lt2 (ord_lt_le h2) h1 with ⟨δ, h3, h4⟩;
  have h4 := cof_trans cfo_spec.1 h4;
  have h5 := cfo_spec.2 _ h4; exact belong_to_self (ord_lt_le_trans h2 (ord_le_trans h5 h3))
noncomputable def cf (α : lim_ord) : inf_card := ⟨cfo α.val, cf_is_card, lim_ord_cf_inf⟩
notation "cf(" α ")" => cf α

theorem cof_cf_le {α β} : cof α.val β → cf(α).val ≤ β := cfo_spec.2 _

theorem inf_card_is_lim_ord {α : inf_card} : α.val ∈ K2 := by
  have h := k12 α.val; cases h with
  | inr => assumption;
  | inl h => exfalso; cases h with
    | inl h => have h1 := α.prop; rw [h] at h1; apply h1.2;
                apply lt_omega_finite; exact ord_k2_gt_0 omega_in_K2;
    | inr h =>
      rcases h with ⟨β, h⟩; have h1 := α.prop; rw [h] at h1;
      have h2 := ord_infinite_iff.1 h1.2; have h3 := cardinal_card.1 h1.1;
      rw [ord_le, or_iff_not_imp_right] at h2;
      have h4 := ord_lt_succ_iff.1 (h2 (K2_not_succ omega_in_K2));
      have h5 := inf_ord_eqv_add_one h4;
      have h6 := (@card_def1 (succ β).val ⟨_, eqv_refl⟩).2; rw [←h3] at h6;
      have h6 := h6 β (eqv_symm h5); exact belong_to_self (ord_lt_le_trans ord_lt_succ h6);
@[implicit_reducible] instance inf_card.coe_lim_ord : Coe inf_card lim_ord :=
  ⟨fun α ↦ ⟨α.val, inf_card_is_lim_ord⟩⟩

def regular (α : ordinal) := cf(ℵ_(α)) = ℵ_(α)
def singular (α : ordinal) := cf(ℵ_(α)) < ℵ_(α)
def weakly_inaccessible (α : ordinal) := α.val ∈ K2 ∧ regular α
def inaccessible (α : ordinal) := weakly_inaccessible α ∧
  ∀ x, |x| < ℵ_(α).val → |P(x)| < ℵ_(α).val

theorem weakly_inaccessible_fix_point {α : ordinal} (h : weakly_inaccessible α) :
  ℵ_(α).val = α := by
  apply ord_le_antisymm; swap;
  · have h2 := monotone_ge_value aleph_smo α; simp only [← Aleph_spec.1.1.2] at h2;
    have h2 := h2 α.prop; exact h2;
  rcases h with ⟨h1, h2⟩; have h4 := cof_aleph h1;
  have h5 : ℵ_(α).val = ℵ_(α).to_lim_ord.val := rfl; rw [h5] at h4;
  have h3 := cof_cf_le h4; unfold regular at h2; rwa [←h2];

end zfset
