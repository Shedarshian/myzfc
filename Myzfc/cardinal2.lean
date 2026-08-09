import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal
import Myzfc.ac

namespace zfset

def limit_point (x : ordset) (α : ordinal) := ∪(x ∩ α) = α
def unbounded_sset (c : ordset) (κ : inf_card) := c s⊆ κ ∧ ∀ α o∈ κ, ∃ β o∈ c, α < β
def close_sset (c : ordset) (κ : inf_card) := c s⊆ κ ∧ ∀ α o∈ κ, limit_point c α → α ∈ c
def close_unbound_sset (c : ordset) (κ : inf_card) := unbounded_sset c κ ∧ close_sset c κ
def stationary_sset (s : ordset) (κ : inf_card) := s s⊆ κ ∧ ∀ c, close_unbound_sset c κ → s ∩ c ≠ o0
def mahlo (α : ordinal) :=
  inaccessible α ∧ stationary_sset {ℵ_(γ).val o// γ o∈ α // regular ℵ_(γ)} ℵ_(α)

theorem limit_point_inter [has_belong β] [has_intersection ordset β] {d : β} :
  limit_point (c ∩ d) α → limit_point c α := by
  unfold limit_point; intro h; apply ord_le_antisymm; · exact ordset_inter_union_le_sup;
  conv => lhs; rw [←h];
  intro x; simp only [has_union.proof_union]; aesop;

theorem close_unbound_intersection [dc : Fact DC] (hk1 : ℵ_(o0) < κ)
  (hk2 : regular κ) (h1 : close_unbound_sset c κ) (h2 : close_unbound_sset d κ) :
  close_unbound_sset (c ∩ d) κ := by
  have h : c ∩ d s⊆ κ; · intro x hx; rw [intersection_def] at hx; exact h1.1.1 _ hx.1;
  constructor <;> use h <;> intro α ha; swap;
  · intro h; rw [ord_belonged_to, intersection_def]; use h1.2.2 α ha (limit_point_inter h);
    rw [intersection_comm] at h; exact h2.2.2 α ha (limit_point_inter h);
  let H : Class := fun p ↦ ∃ x o∈ c, ∃ y o∈ d, ∃ z o∈ c, ∃ a o∈ d,
        p = s⟨s⟨x.val, y.val⟩, s⟨z.val, a.val⟩⟩ ∧ y < z ∧ z < a
  have g1 : H s⊆ (c.val × d.val) × (c.val × d.val);
  · intro x; unfold H; simp [proof_in_Class]; intros; subst x; aesop;
  have g2 := subseteq_is_set g1; let Hs : set := H.to_set g2;
  have g3 : is_total Hs (c.val × d.val);
  · intro x x1; rw [has_product.proof_product] at x1;
    rcases x1 with ⟨a, a1, b, a2, a3⟩; let a' : ordinal := ⟨a, c.prop _ a1⟩;
    let b' : ordinal := ⟨b, d.prop _ a2⟩;
    rcases h1.1.2 b' (h2.1.1 _ a2) with ⟨α, x2, x3⟩;
    rcases h2.1.2 α (h1.1.1 _ x2) with ⟨β, x4, x5⟩;
    use s⟨α.val, β.val⟩; simp only [pair_in_product]; use ⟨x2, x4⟩;
    unfold Hs; rw [Class_to_set_ext, proof_in_Class]; unfold H;
    subst x; simp only [ordered_pair_eq_iff]; use ⟨a, c.prop _ a1⟩; use a1;
    use ⟨b, d.prop _ a2⟩; use a2; use α; use x2; use β;
  rcases h1.1.2 α ha with ⟨a1, d1, d2⟩; rcases h2.1.2 a1 (h1.1.1 _ d1) with ⟨a2, d3, d4⟩;
  have d5 : s⟨a1.val, a2.val⟩ ∈ c.val × d.val; · simp only [pair_in_product]; exact ⟨d1, d3⟩;
  rcases dc.out _ _ g3 _ d5 with ⟨f, d6, d7, d8⟩; let bc := W(f);
  have b1 : bc s⊆ c.val × d.val;
  · intro x; unfold bc; simp [has_function.proof_range]; intro y y1;
    have y2 := (has_function.proof_domain _).2 ⟨_, y1⟩; rw [←d6.2] at y2;
    let y : ordinal := ⟨y, ord_element_ord _ _ y2⟩; have y3 := value_func d6.1.2 y1; rw [←y3];
    apply @nat.induction (fun y ↦ f[[y.val.val]] ∈ c.val × d.val) ⟨y, y2⟩;
    · convert_to f[[s0]] ∈ c.val × d.val; · rfl;
      rw [d7]; simp only [pair_in_product]; exact ⟨d1, d3⟩;
    intro n y4; have y5 := d8 n.val n.prop; simp only at y5; unfold Hs at y5;
    rw [Class_to_set_ext, proof_in_Class] at y5; unfold H at y5;
    rcases y5 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2⟩; simp only [ordered_pair_eq_iff] at a9;
    convert_to s⟨a5.val, a7.val⟩ ∈ c.val × d.val; · rw [←a9.2]; rfl;
    simp only [pair_in_product]; exact ⟨a6, a8⟩;
  let bl' := {Pr1[[x]] // x s∈ bc}; let br' := {Pr2[[x]] // x s∈ bc};
  have l1 := Pr1_sset b1; have r1 := Pr2_sset b1;
  let bl : ordset := ⟨bl', subseteq_trans l1 c.prop⟩;
  let br : ordset := ⟨br', subseteq_trans r1 d.prop⟩; use ∪(bl);
  have l2 : ∀ a o∈ bl, ∃ b o∈ br, a < b;
  · intro a a4; unfold bl at a4; rw [ord_belonged_to, set_ordset_belong] at a4; simp only at a4;
    rw [replacement_notation_def] at a4; rcases a4 with ⟨c, a4, a5⟩; have a3 := b1 _ a4;
    rw [has_product.proof_product] at a3; rcases a3 with ⟨d, a6, e, a7, _⟩; subst c;
    simp only [Pr1_value] at a5; subst d; use ⟨e, d.prop _ a7⟩;
    unfold br; rw [ord_belonged_to, set_ordset_belong]; simp only;
    rw [replacement_notation_def]; constructor; · use s⟨a.val, e⟩; use a4; simp only [Pr2_value];
    unfold bc at a4; simp only [has_function.proof_range] at a4; rcases a4 with ⟨a8, a9⟩;
    have b3 := (has_function.proof_domain _).2 ⟨_, a9⟩; rw [←d6.2] at b3;
    have a9 := value_func d6.1.2 a9;
    let a8' : ordinal := ⟨a8, ord_element_ord _ _ b3⟩; cases @nat_two_type a8' b3 with
    | inl b4 =>
      have b5 : a8 = s0 := Subtype.coe_inj.2 b4; subst a8; rw [d7] at a9;
      simp only [ordered_pair_eq_iff] at a9; convert_to a1 < a2; · symm; exact Subtype.ext a9.1;
      · symm; exact Subtype.ext a9.2;
      assumption;
    | inr b4 =>
      rcases b4 with ⟨y, b4⟩; have b5 : a8' < ω := b3; rw [b4] at b5;
      have b6 := d8 y (ord_lt_trans ord_lt_succ b5); simp only at b6;
      rw [Class_to_set_ext, proof_in_Class] at b6; rcases b6 with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩;
      simp only [ordered_pair_eq_iff] at c9; rw [←b4] at c9; unfold a8' at c9; simp only at c9;
      rw [a9] at c9; simp only [ordered_pair_eq_iff] at c9; rw [Subtype.ext c9.2.1];
      convert_to c5 < c7; · exact Subtype.ext c9.2.2;
      exact c10.2;
  have l3 : ∀ a o∈ br, ∃ b o∈ bl, a < b;
  · intro a a4; unfold br at a4; rw [ord_belonged_to, set_ordset_belong] at a4; simp only at a4;
    rw [replacement_notation_def] at a4; rcases a4 with ⟨c, a4, a5⟩; have a3 := b1 _ a4;
    rw [has_product.proof_product] at a3; rcases a3 with ⟨d, a6, e, a7, _⟩; subst c;
    simp only [Pr2_value] at a5; subst e;
    unfold bc at a4; simp only [has_function.proof_range] at a4; rcases a4 with ⟨a8, a9⟩;
    have b3 := (has_function.proof_domain _).2 ⟨_, a9⟩; rw [←d6.2] at b3;
    have a9 := value_func d6.1.2 a9;
    let a8' : ordinal := ⟨a8, ord_element_ord _ _ b3⟩;
    have b6 := d8 a8' b3; simp only at b6;
    rw [Class_to_set_ext, proof_in_Class] at b6; rcases b6 with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩;
    simp only [ordered_pair_eq_iff] at c9; unfold a8' at c9; simp only at c9;
    rw [a9] at c9; simp only [ordered_pair_eq_iff] at c9; rw [Subtype.ext c9.1.2]; use c5;
    constructor; swap; · exact c10.1;
    unfold bl; rw [ord_belonged_to, set_ordset_belong]; simp only;
    rw [replacement_notation_def]; use s⟨c5.val, c7.val⟩; unfold bc;
    rw [Pr1_value, ←c9.2]; simp only [and_true]; rw [has_function.proof_range]; use (succ a8').val;
    apply value_func2 d6.1.2; rw [←d6.2]; apply ord_k2_succ_in omega_in_K2; exact b3;
  have lr : ∪(bl) = ∪(br);
  · apply ord_le_antisymm;
    · apply ordset_union_sup_le; intro α l4; rcases l2 α l4 with ⟨β, l5, l6⟩; apply ord_lt_le;
      exact ord_lt_le_trans l6 (ordset_union_le_sup _ l5);
    · apply ordset_union_sup_le; intro α l4; rcases l3 α l4 with ⟨β, l5, l6⟩; apply ord_lt_le;
      exact ord_lt_le_trans l6 (ordset_union_le_sup _ l5);
  constructor; swap;
  · apply ord_lt_le_trans d2; apply ordset_union_le_sup; rw [ord_belonged_to, set_ordset_belong];
    unfold bl; simp only; rw [replacement_notation_def]; use s⟨a1.val, a2.val⟩;
    simp only [Pr1_value, and_true]; unfold bc; simp only [has_function.proof_range]; use s0;
    rw [←d7]; apply value_func2 d6.1.2; rw [←d6.2]; exact ord_k2_gt_0 omega_in_K2;
  rw [ord_belonged_to, intersection_def]; constructor;
  · apply h1.2.2; swap;
    · unfold limit_point; rw [←extensionality_belong]; intro x;
      simp [has_union.proof_union]; constructor <;> intro ⟨u1, u2, u3⟩;
      · rcases u3 with ⟨u3, u4, u5, u6⟩; use u4; use (bl.prop _ u6).1 _ u5 _ u2;
      use u1; use u2; use l1 _ u3; rcases l2 ⟨u1, (bl.prop _ u3)⟩ u3 with ⟨u4, u5, u6⟩;
      rcases l3 _ u5 with ⟨u7, u8, u9⟩; use u7.val; use ord_lt_trans u6 u9; use u8;
    convert_to ∪(bl) < κ.val; · rfl;
    rw [ord_lt]; constructor;
    · intro x; simp [has_union.proof_union]; intro y y1 y2;
      refine κ.val.prop.1 _ ?_ _ y1; apply h1.1.1; exact l1 _ y2;
    intro l4; suffices k1 : cof κ.val ω;
    · have k1 := cfo_spec.2 _ k1; have k2 := Subtype.coe_inj.2 hk2; unfold cf at k2;
      simp only at k2; rw [k2] at k1; rw [←aleph_0_eq_omega] at k1;
      exact belong_to_self (ord_le_lt_trans k1 hk1);
    let f2 := {s⟨n.val, Pr1[[f[[n.val]]]]⟩ // n o∈ ω};
    apply cof_union2 omega_in_K2;

  -- · suffices b2 : a1.val ∈ bc; · exact ord_lt_le_trans d2 (ordset_union_le_sup _ b2);
  --   unfold bc; rw [set_ordset_belong]; simp only; rw [has_function.proof_range, ←d4]; use s0;
  --   have d6 : s0 ∈ D(f); · rw [←d3.2]; exact ord_k2_gt_0 omega_in_K2;
  --   exact value_func2 d3.1.2 d6;
  -- 好像不对，DC可能不能证



theorem mahlo_fix_point (α : ordinal) : mahlo α → count inaccessible α = α := by sorry

end zfset
