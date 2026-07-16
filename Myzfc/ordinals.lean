import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2

namespace zfset

def is_transitive
  {α : Type u} [s : has_belong α] (a : α) : Prop :=
∀ x : set, x ∈ a → x s⊆ a
notation "Tr(" a ")" => is_transitive a
def is_ordinal
  {α : Type u} [s : has_belong α] (a : α) : Prop :=
Tr(a) ∧ (∀ x : set, x ∈ a → ∀ y : set, y ∈ a → x ∈ y ∨ x = y ∨ y ∈ x)
notation "Ord(" a ")" => is_ordinal a

theorem transitive_belong_subset {A B : Class} (h1 : Tr(A)) :
B ∈ A → B s⊂ A :=
by
  intro h;
  have f := class_belong_is_set h;
  rcases f with ⟨x, f⟩;
  rw [← f, set_to_class_belong] at h;
  have h1 := h1 x h;
  rw [← f]; use h1;
  intro g; rw [← g] at h;
  exact belong_to_self h;

theorem transitive_belong_subset_set {A : Class} {B : set} (h1 : Tr(A)) :
B ∈ A → ↑B s⊂ A :=
by
  intro h;
  have h1 := h1 B h;
  use h1;
  intro g; rw [← g] at h;
  exact belong_to_self h;

theorem transitive_subset_iff_belong
  (A B : Class) (h1 : Ord(A)) (h2 : Tr(B)) :
B s⊂ A ↔ B ∈ A :=
by
  apply Iff.intro <;> intro h;
    swap; · exact transitive_belong_subset h1.1 h;
  have f := subset_sub_nonempty h;
  have f := axiom_of_regularity_strong f;
  rcases f with ⟨x, ⟨⟨f1, f3⟩, f2⟩⟩;
  have h3 := h1.1 _ f1;
  rw [← extensionality_belong] at f2;
  have h4 : x s⊆ B;
  · intro a;
    have f2 := f2 a;
    rw [empty_false] at f2; simp only [iff_false] at f2;
    erw [has_intersection.proof_intersection] at f2;
    push Not at f2;
    intro hx; have f2 := f2 hx;
    unfold_projs at f2;
    push Not at f2; erw [proof_in_Class] at f2;
    push Not at f2; apply f2;
    exact h3 _ hx;
  have hb : B = x; swap;
  · rw [hb]; erw [set_to_class_belong]; exact f1;
  apply subseteq_antisymm; swap; · exact h4;
  intros y hy;
  have hya := h.1 _ hy;
  have hxy := h1.2 _ f1 _ hya;
  cases hxy with
  | inr hxy =>
    cases hxy with
    | inr hxy => exact hxy;
    | inl hxy => rw [← hxy] at hy; contradiction;
  | inl hxy => have hy := h2 _ hy x hxy; contradiction;

theorem transitive_subset_iff_belong_set
  (A : Class) (B : set) (h1 : Ord(A)) (h2 : Tr(B)) :
↑B s⊂ A ↔ B ∈ A :=
by
  erw [transitive_subset_iff_belong _ _ h1 h2, set_to_class_belong];

theorem transitive_subset_iff_belong_set_set
  (A B : set) (h1 : Ord(A)) (h2 : Tr(B)) :
B s⊂ A ↔ B ∈ A :=
by
  erw [← transitive_subset_iff_belong_set _ _ h1 h2];
  apply Iff.intro <;> intro h <;> constructor;
  · intro x; exact h.1 x;
  · intro h3;
    erw [← set_eq_iff_class] at h3; exact h.2 h3;
  · intro x; exact h.1 x;
  intro h3; rw [h3] at h;
  have h4 := h.2;
  apply h4; rfl;

theorem ord_element_ord'
  {α : Type u} [s : has_belong α] (A : α) (a : set) (h : Ord(A)) :
a ∈ A → Ord(a) :=
by
  intro ha;
  have h1 := h.1 _ ha; constructor <;>
  intros x hx y hy;
  swap;
    all_goals have h2 := h1 _ hx;
  · have h3 := h1 _ hy;
    exact h.2 x h2 y h3;
  have h2 := h.1 _ h2 _ hy;
  have h3 := h.2 _ ha _ h2;
  cases h3 with
  | inl h3 => exfalso; exact belong_to_3 hx h3 hy;
  | inr h3 =>
    cases h3 with
    | inl h3 => subst a; exfalso; exact belong_to_2 hx hy;
    | inr h3 => assumption;

theorem ordinal_class_intersection
  (A B : Class) (h1 : Ord(A)) (h2 : Ord(B)) : Ord(A ∩ B) :=
by
  constructor <;> intros x h;
  · erw [has_intersection.proof_intersection] at h;
    rw [← transitive_subset_iff_belong_set] at h;
    any_goals exact h1;;
    rw [← transitive_subset_iff_belong_set] at h;
    · intro y hy;
      erw [has_intersection.proof_intersection];
      use h.1.1 y hy;
      use h.2.1 y hy;
    any_goals assumption;;
    any_goals exact (ord_element_ord' _ _ h2 h.2).1;;
  intros y hy;
  erw [has_intersection.proof_intersection] at *;
  exact h1.2 _ h.1 _ hy.1;

theorem ordinal_class_order
  (A B : Class) (h1 : Ord(A)) (h2 : Ord(B)) :
A ∈ B ∨ A = B ∨ B ∈ A :=
by
  have h : ¬(A ∩ B s⊂ A ∧ A ∩ B s⊂ B);
  · intro ⟨h3, h4⟩;
    have oab := ordinal_class_intersection _ _ h1 h2;
    rw [transitive_subset_iff_belong _ _ h1 oab.1] at *;
    rw [transitive_subset_iff_belong _ _ h2 oab.1] at *;
    have he := class_belong_is_set h3;
    rcases he with ⟨ab, he⟩;
    rw [← he] at h3 h4 oab;
    rw [set_to_class_belong] at *;
    have hab : ab ∈ ab.to_Class;
    · rw [he];
      exact And.intro h3 h4;
    exact belong_to_self hab;
  unfold subset at h;
  rw [and_assoc] at h;
  -- rw [← and_assoc _ (A ∩ B s⊆ B)] at h;
  push Not at h;
  have h := h intersection_subseteq_left;
  rw [Imp.swap] at h;
  have h := h intersection_subseteq_right;
  rw [← or_iff_not_imp_left] at h;
  cases' h with h h <;>
    rw [eq_comm] at h; swap; rw [intersection_comm] at h;
    all_goals
      rw [← subseteq_iff_eq_intersection] at h;
      rw [subseteq_iff_subset_eq] at h;
      rw [transitive_subset_iff_belong] at h;;
    any_goals
      first | assumption | exact h2.1 | exact h1.1;;;
    · right; rw [or_comm, eq_comm]; assumption;
  rw [← or_assoc]; left; assumption;

theorem ordinal_set_order
  (A B : set) (h1 : Ord(A)) (h2 : Ord(B)) :
A ∈ B ∨ A = B ∨ B ∈ A :=
by
  have h := ordinal_class_order A.to_Class B.to_Class h1 h2;
  rw [set_to_class_belong, set_to_class_belong] at h;
  cases h with
  | inl => left; assumption;
  | inr h => right; cases h with
    | inl h =>
      left; rw [← extensionality_belong];
      intro a;
      unfold set.to_Class at h;
      have f : (fun (x : set) => belong_set x A) a ↔
        (fun (x : set) => belong_set x B) a;
      · rw [h];
      exact f;
    | inr => right; assumption;

def On : Class := fun x => Ord(x)
def ordinal := {x : set // Ord(x)}

theorem subset_On_tr_is_ordinal (a : set) :
Tr(a) ∧ a s⊆ On → Ord(a) :=
by
  intro h; use h.1;
  intro x hx y hy;
  have hx := h.2 _ hx;
  have hy := h.2 _ hy;
  apply ordinal_set_order; assumption';

theorem On_is_ordinal_class : Ord(On) :=
by
  constructor <;> intro x hx y;
  · exact ord_element_ord' _ _ hx;
  exact ordinal_set_order _ _ hx;

theorem On_proper_class : Class.is_proper On :=
by
  intro h;
  rcases h with ⟨a, h⟩;
  have hn : Ord(On) := On_is_ordinal_class;
  rw [← h] at hn;
  have ha : a ∈ On := hn;
  rw [← h] at ha;
  exact belong_to_self ha;

theorem Ord_in_On_or_eq_On (A : Class) (h : Ord(A)) : A ∈ On ∨ A = On :=
by
  have f := ordinal_class_order A On h On_is_ordinal_class;
  rw [← or_assoc] at f;
  cases f with
  | inl => assumption;
  | inr f =>
    exfalso;
    have g := class_belong_is_set f;
    exact On_proper_class g;

theorem ordinal_class_transitive (A : Class) (h : A s⊆ On) (ht : Tr(A)) :
  Ord(A) :=
by
  constructor; · assumption;
  intros x f;
  have hf := h x f;
  intros y g; have hg := h y g;
  apply On_is_ordinal_class.2; assumption';

instance ordinal.to_has_belong : has_belong ordinal :=
⟨
  fun x y => y ∈ x.val,
  by {
    intros x y; rw [extensionality_belong, Iff.comm];
    exact Subtype.ext_iff
  },
  fun α => α.val.to_Class,
  by {intros; rfl},
  fun α => True
⟩

theorem ord_class {a : set} : Ord(a) ↔ Ord(a.to_Class) := Iff.rfl

def ordinal.belonged_to {β : Type _} [s : has_belong β] (a : ordinal) (b : β) :
Prop := has_belong.belong b a.val
instance ordinal.to_has_belonged_to : has_belonged_to ordinal :=
⟨ @ordinal.belonged_to ⟩

theorem ord_element_ord (A : ordinal) (a : set) : a ∈ A → Ord(a) :=
  ord_element_ord' A.val a A.prop

noncomputable instance ordinal.to_has_union : has_union ordinal :=
⟨ fun a => ⟨make_union a.val, by {
  rcases a with ⟨a, pa⟩;
  constructor <;> intros x hx y hy <;>
    rw [axiom_of_union] at *;
  · rcases hx with ⟨y2, hx⟩;
    have hx := pa.1 y2 hx.2 x hx.1;
    use x;
  rcases hx with ⟨y2, hx⟩;
  rcases hy with ⟨y1, hy⟩;
  apply pa.2;
  · apply pa.1; · exact hx.2;
    exact hx.1;
  apply pa.1; · exact hy.2;
  exact hy.1;
} ⟩, by {
  intro a; apply axiom_of_union;
} ⟩

noncomputable instance ordinal.to_has_binary_union : has_binary_union ordinal :=
⟨
  fun x y => ⟨ x.val ∪ y.val, by {
    have h := ordinal_set_order x.val y.val x.prop y.prop;
    rw [← transitive_subset_iff_belong_set_set] at h;
    rw [← transitive_subset_iff_belong_set_set] at h;
    any_goals first | exact x.prop | exact y.prop | exact x.prop.1 | exact y.prop.1;;
    cases' h with h h; swap; cases' h with h h;
    rw [h]; simp; exact y.prop;
    all_goals unfold subset at h;;
    all_goals erw [subseteq_iff_eq_union] at h;
    rw [binary_union_comm];
    any_goals rw [← h.1];
    any_goals first | exact x.prop | exact y.prop;;;
  } ⟩,
  by { intros; erw [union_set_is_union]; rfl; }
⟩

noncomputable instance ordinal.to_has_intersection : has_intersection ordinal ordinal :=
⟨
  fun x y => ⟨ x.val ∩ y.val, by {
    constructor <;> intros x1 hx y1 hy <;>
    erw [has_intersection.proof_intersection] at *;
    · rcases hx with ⟨hx1, hx2⟩;
      use x.prop.1 _ hx1 _ hy;
      use y.prop.1 _ hx2 _ hy;
    exact x.prop.2 _ hx.1 _ hy.1;
  }
  ⟩, by {
    intros; erw [@has_intersection.proof_intersection set set]; rfl;
  }
⟩

instance : has_intersection Class ordinal :=
⟨ fun A B x => x ∈ A ∧ x ∈ B, by {intros; rfl} ⟩

noncomputable instance : has_intersection set ordinal :=
⟨ fun A B => A ∩ B.val, by {intros; simp only [intersection_def, and_congr_right_iff]; intro; rfl} ⟩

@[simp] theorem ord_subseteq {α β : ordinal} :
α s⊆ β ↔ α.val s⊆ β.val := by {rfl}

@[simp] theorem ord_subset {α β : ordinal} :
α s⊂ β ↔ α.val s⊂ β.val :=
by
  apply Iff.intro <;> intro h <;> constructor;
  · have h := h.1;
    · rwa [ord_subseteq] at h;
  · have h := h.2; simp only [ne_eq]; intro f;
    exact h (Subtype.ext f);
  · have h := h.1;
    rwa [ord_subseteq];
  · have h := h.2; simp only [ne_eq];
    intro f; erw [f] at h;
    simp at h;

theorem ord_subset_iff_belong {α β : ordinal} :
α ∈ β ↔ α s⊂ β :=
by
  apply Iff.symm;
  erw [← transitive_subset_iff_belong_set_set β.val α.val β.prop α.prop.1];
  simp;

instance ordinal.to_has_lt : LT ordinal :=
⟨ belong ⟩

instance ordinal.to_has_le : LE ordinal :=
⟨ subseteq ⟩

instance ord_lt_is_irrefl : @Std.Irrefl ordinal LT.lt :=
⟨ by {intro a; exact belong_to_self} ⟩

instance ord_preorder : Preorder ordinal :=
⟨
  by {intro a; unfold_projs; rfl},
  @subseteq_trans ordinal ordinal ordinal _ _ _,
  by {
    intros a b; unfold_projs; rw [ord_subset_iff_belong];
    exact subset_iff_subseteq_not_subseteq},
⟩

instance ord_partial_order : PartialOrder ordinal :=
⟨
  @subseteq_antisymm ordinal _
⟩
theorem ord_le_antisymm {α β : ordinal} : α ≤ β → β ≤ α → α = β := subseteq_antisymm

theorem ord_total {α β : ordinal} : α < β ∨ α = β ∨ β < α := by
  cases ordinal_set_order α.val β.val α.prop β.prop with
  | inl h => left; exact h;
  | inr h => right; cases h with
    | inr h => right; exact h;
    | inl h => left; exact Subtype.ext h;

theorem ord_belong {α β : ordinal} : α ∈ β ↔ α.val ∈ β.val := by rfl;
theorem set_ord_belong {α : set} {β : ordinal} : α ∈ β ↔ α ∈ β.val := by rfl;

noncomputable def succ (α : ordinal) : ordinal :=
⟨
  succ_set α.val,
  by {
  constructor <;> intros x hx y hy <;>
  erw [has_binary_union.proof_union] at * <;>
  cases' hx with hx hx; any_goals cases' hy with hy hy;;
  · left; exact α.prop.1 _ hx _ hy;
  any_goals rw [element_in_one_element_set] at *;;
  · left; rwa [hx] at hy;
  · exact α.prop.2 _ hx _ hy;
  · rw [hy]; left; assumption;
  · rw [hx]; right; right; assumption;
  rw [hx, hy]; right; left; rfl;
}⟩

theorem ord_lt_succ_iff {a b : ordinal} : a < succ b ↔ a ≤ b :=
by
  unfold_projs; unfold succ;
  erw [union_set_is_union];
  rw [@element_in_one_element_set];
  erw [ord_subset_iff_belong];
  apply Iff.intro <;> intro h;
  cases h with
  | inl h => exact h.1;
  | inr h =>
    have h := Subtype.ext h;
    · rw [h];
  have g := em (a = b);
  cases g with
  | inl g => right; rw [g];
  | inr g => left; use h;

theorem ord_class_union_ordinal [has_belong α] [has_union α] (A : α)
(h : A s⊆ On) : Ord(∪(A)) :=
by
  constructor <;> intros x hx y hy;
  · erw [has_union.proof_union] at *;
    rcases hx with ⟨c, ⟨hx1, hx2⟩⟩;
    use c;
    have hx3 := h _ hx2;
    use hx3.1 _ hx1 _ hy;
  erw [has_union.proof_union] at hx hy;
  rcases hx with ⟨c1, ⟨hx1, hx2⟩⟩;
  rcases hy with ⟨c2, ⟨hy1, hy2⟩⟩;
  have hx3 := h _ hx2;
  have hy3 := h _ hy2;
  have hx4 := ord_element_ord' _ _ hx3 hx1;
  have hy4 := ord_element_ord' _ _ hy3 hy1;
  exact ordinal_set_order x y hx4 hy4;

theorem ord_lt_succ {α : ordinal} : α < succ α :=
by
  unfold_projs;
  erw [union_set_is_union];
  right; simp;

theorem ord_no_between_succ {α β : ordinal} : ¬(α < β ∧ β < succ α) :=
by
  intro h; rcases h with ⟨h1, h2⟩;
  unfold_projs at *;
  erw [union_set_is_union] at h2;
  cases h2 with
  | inl h2 =>
    exact belong_to_2 h1 h2;
  | inr h2 =>
    rw [element_in_one_element_set] at h2;
    have h2 := Subtype.ext h2;
    rw [h2] at h1; exact belong_to_self h1;

theorem ord_succ_belong {α β : ordinal} : α < β → succ α = β ∨ succ α < β := by
  intro h; by_cases ha : succ α = β; · left; assumption;
  right; have he := @ord_total (succ α) β;
  cases he with
  | inl => assumption;
  | inr he => cases he with
    | inl => contradiction;
    | inr he => exfalso; exact ord_no_between_succ ⟨h, he⟩

@[refl] theorem ord_le_self {α : ordinal} : α ≤ α := by {unfold_projs; rfl}

theorem ord_nlt_self {α : ordinal} : ¬(α < α) := belong_to_self

theorem ord_le {α β : ordinal} : α ≤ β ↔ α < β ∨ α = β :=
by
  unfold_projs;
  erw [ord_subset_iff_belong];
  unfold subset;
  rw [and_or_right];
  constructor <;> intro h;
  constructor; · left; assumption;
  · rw [Or.comm];
    exact em _;
  have h := h.1;
  cases h with
  | inl => assumption;
  | inr h => rw [h];

theorem ord_lt {α β : ordinal} : α < β ↔ α ≤ β ∧ α ≠ β :=
by
  rw [ord_le, or_and_right];
  simp only [ne_eq, and_not_self, or_false, iff_self_and];
  intros h1 h2; rw [h2] at h1;
  exact ord_nlt_self h1;

theorem ord_lt_le {α β : ordinal} : α < β → α ≤ β :=
by {rw [ord_lt]; intro h; exact h.1}
theorem ord_nle {α β : ordinal} : ¬α ≤ β ↔ β < α := by
  rw [ord_le]; use Or.resolve_left (or_assoc.2 (@ord_total α β));
  intro h g; cases g with
  | inl g => exact belong_to_2 h g;
  | inr g => rw [g] at h; exact belong_to_self h;

theorem ord_succ_belong_le {α β : ordinal} : α < β → succ α ≤ β :=
  fun h => ord_le.2 (Or.symm (ord_succ_belong h))

@[trans] theorem ord_le_trans {α β γ : ordinal} : α ≤ β → β ≤ γ → α ≤ γ :=
subseteq_trans
@[trans] theorem ord_lt_trans {α β γ : ordinal} : α < β → β < γ → α < γ :=
by
  intros h1 h2;
  rw [ord_lt] at *;
  use ord_le_trans h1.1 h2.1;
  intro x;
  rw [← ord_lt] at *;
  rw [x] at h1; exact belong_to_2 h1 h2;
@[trans] theorem ord_le_lt_trans {α β γ : ordinal} : α ≤ β → β < γ → α < γ :=
by
  intros h1 h2; rw [ord_le] at h1;
  cases h1 with
  | inl => apply ord_lt_trans; assumption';
  | inr h1 => rw [h1]; assumption';
@[trans] theorem ord_lt_le_trans {α β γ : ordinal} : α < β → β ≤ γ → α < γ :=
by
  intros h1 h2; rw [ord_le] at h2;
  cases h2 with
  | inl => apply ord_lt_trans; assumption';
  | inr h2 => rw [←h2]; assumption';

theorem ord_succ_le_succ {α β : ordinal} : α ≤ β → succ α ≤ succ β :=
  fun h => ord_succ_belong_le (ord_le_lt_trans h ord_lt_succ)

theorem ord_succ_lt_succ {α β : ordinal} : α < β → succ α < succ β :=
  fun h => ord_le_lt_trans (ord_succ_belong_le h) ord_lt_succ

noncomputable def o0 : ordinal := ⟨s0, by {
  constructor <;> intros x hx y hy <;>
  exfalso <;> apply axiom_of_empty hx;
}⟩
theorem o0_eq_s0 : o0.val = s0 := rfl

def K1 : Class := fun a => ∃ h : Ord(a), (a = s0 ∨ ∃ β : ordinal, ⟨a, h⟩ = (succ β))
def K2 : Class := On - K1
axiom omega_s : set
theorem k12 (α : ordinal) : (α = o0 ∨ ∃ β : ordinal, α = succ β) ∨ α.val ∈ K2 := by
  unfold K2; unfold_projs; simp only;
  conv => rhs; rw [proof_in_Class, And.comm];
  by_cases h : ↑α ∈ K1;
  · left; rcases h with ⟨ho, h⟩;
    cases h with
    | inl h => left; exact Subtype.ext h;
    | inr h => right; exact h;
  right; constructor; · assumption;
  exact α.prop;
theorem ord_in_k2 {α : ordinal} :
  α.val ∈ K2 ↔ ¬α = o0 ∧ ¬∃ β : ordinal, α = succ β := by
  unfold K2; unfold_projs; erw [proof_in_Class]; simp only [not_exists];
  constructor <;> intro h;
  · have h := h.2; unfold K1 at h; erw [proof_in_Class] at h;
    push Not at h; rcases h α.prop with ⟨h1, h2⟩; constructor;
    · intro ha; rw [ha] at h1; contradiction;
    push Not; intro β; exact h2 β;
  use α.prop; unfold K1; erw [proof_in_Class];
  simp only [Subtype.coe_eta, exists_prop, not_and, not_or, not_exists]; intro;
  constructor;
  · intro h2; have h := h.1; rw [←o0_eq_s0] at h2;
    have h2 := Subtype.ext h2; contradiction;
  intro x; exact h.2 x;

noncomputable def pred (α : ordinal) : ordinal :=
⟨ pred_set α.val, by
  by_cases h : ∃ b, α.val = succ_set b;
  · rcases h with ⟨b, h⟩; rw [h, ←succ_pred_set];
    have h2 : b ∈ α.val; · rw [h]; exact self_belong_succ;
    apply ord_element_ord' α _ α.prop h2;
  unfold pred_set; simp only [h, ↓reduceDIte]; exact o0.prop;
⟩

theorem succ_pred (α : ordinal) : α = pred (succ α) := by
  apply Subtype.ext; unfold pred succ; simp only; exact succ_pred_set _;

theorem pred_succ (α : ordinal) (h : α ∈ K1 ∧ ¬α = o0) :
  α = succ (pred α) := by
  rcases h with ⟨⟨ho, h1⟩, h2⟩;
  cases h1 with
  | inl h1 => rw [←o0_eq_s0] at h1; have h1 := Subtype.ext h1; contradiction;
  | inr h1 =>
    rcases h1 with ⟨x, h1⟩;
    have ha : ⟨α.val, ho⟩ = α; · apply Subtype.ext; rfl;
    rw [ha] at h1; rw [h1]; congr; exact succ_pred _;

theorem union_succ {α : ordinal} : ∪(succ α) = α := by
  rw [←extensionality_belong]; intro x; erw [has_union.proof_union];
  constructor <;> intro h;
  · rcases h with ⟨c, h1, h2⟩; have h3 := (succ α).prop.1 c h2 x h1;
    have h3 := belong_succ_iff.1 h3; cases h3 with
    | inl => assumption;
    | inr =>
      subst x; exfalso;
      have hc := ord_element_ord' (succ α) c (succ α).prop h2;
      apply @ord_no_between_succ α ⟨c, hc⟩;
      unfold_projs; use h1; use h2;
  use α.val; use h; exact self_belong_succ;
theorem union_succ_set {α : ordinal} : ∪((succ α).val) = α.val := by
  conv => rhs; rw [←@union_succ α];
  rw [←extensionality_belong]; intro x; rfl;

axiom axiom_of_infinity : ∀ x : set, x ∈ omega_s ↔ x s⊆ K1 ∧ x ∈ K1

theorem omega_subset_K1 : omega_s s⊆ K1 :=
by
  intro x;
  rw [axiom_of_infinity];
  intro h; rcases h;
  assumption;

noncomputable def ω : ordinal :=
⟨ omega_s, by {
  apply subset_On_tr_is_ordinal;
  constructor; swap;
  · apply subseteq_trans omega_subset_K1;
    intros x h; exact h.1;
  intros x hx y hy;
  rw [axiom_of_infinity _] at *;
  apply And.symm;
  use hx.1 _ hy;
  intros a h;
  have h2 : a ∈ x := (hx.2.1.1 _ hy _ h);
  exact hx.1 _ h2;
} ⟩

theorem succ_subset_K1 {β : ordinal} : β ∈ ω ↔ (succ β).val s⊆ K1 :=
by
  erw [union_subseteq_iff,
    one_element_set_subseteq,
    axiom_of_infinity];

def nat := {x : ordinal // x ∈ ω}

theorem peano1 : o0 ∈ ω :=
by
  erw [axiom_of_infinity];
  constructor; intros x h;
  · exfalso; erw [empty_false] at h; assumption;
  use o0.prop;
  left; rfl;
noncomputable def n0 : nat := ⟨o0, peano1⟩

theorem peano2 (i : nat) : succ i.val ∈ ω :=
by
  have h := i.prop;
  erw [axiom_of_infinity] at h;
  erw [axiom_of_infinity];
  constructor; intros x hx;
  · erw [belong_succ_iff] at hx;
    cases hx with
    | inl hx => exact h.1 _ hx;
    | inr hx => rw [hx]; exact h.2;
  constructor;
  · right; use i.val;
    rfl;
noncomputable def succ_nat (n : nat) : nat := ⟨succ n.val, peano2 n⟩

theorem peano3 (i : nat) : succ i.val ≠ o0 :=
by
  intro x;
  rw [← @empty_false i.val.val];
  have g : o0.val = s0; · rfl;
  rw [← g]; rw [← x];
  erw [has_binary_union.proof_union];
  simp;

theorem peano4 (i : nat) (j : nat) : succ i.val = succ j.val ↔ i = j :=
by
  constructor <;> intro h; swap;
  · rw [h];
  have ha := @ord_lt_succ i.val;
  rw [h, ord_lt_succ_iff, ord_le] at ha;
  have hb := @ord_lt_succ j.val;
  rw [← h, ord_lt_succ_iff, ord_le] at hb;
  cases' ha with ha ha <;> cases' hb with hb hb;
  rotate_right; exact Subtype.ext ha;
  all_goals exfalso;;
  · exact belong_to_2 ha hb;
  · rw [hb] at ha; exact belong_to_self ha;
  rw [ha] at hb; exact belong_to_self hb;

theorem peano5 (A : Class) : (s0 ∈ A ∧
∀ i : nat, i.val.val ∈ A → (succ i.val).val ∈ A) → ω s⊆ A :=
by
  intro h; rcases h with ⟨h1, h2⟩;
  erw [← Class_sub_empty_iff_subseteq];
  by_contra;
  have hx := axiom_of_regularity_strong this;
  rcases hx with ⟨i, ⟨⟨hx1, h3⟩, hx2⟩⟩;
  erw [axiom_of_infinity] at hx1;
  rcases hx1 with ⟨h4, ⟨hx1, h5⟩⟩;
  cases h5 with
  | inl h5 => rw [h5] at h3; contradiction;
  | inr h5 =>
    rcases h5 with ⟨β, h5⟩;
    have hn : i = (succ β).val; · rw [←h5];
    rw [hn] at h4;
    erw [← succ_subset_K1] at h4;
    have hb2 : β ∈ A;
    · rw [← extensionality_belong] at hx2;
      have hx2 := hx2 β.val;
      rw [empty_false] at hx2; simp only [iff_false] at hx2;
      erw [has_intersection.proof_intersection] at hx2;
      push Not at hx2;
      rw [hn] at hx2;
      have hx2 := hx2 ord_lt_succ;
      by_contra hb; exact hx2 (And.intro h4 hb);
    have hb := h2 ⟨β, h4⟩ hb2;
    erw [← h5] at hb; contradiction;
theorem nat.induction {P : nat → Prop} (n : nat) (h0 : P n0)
  (h : ∀ n, P n → P (succ_nat n)) : P n := by
  let A : Class := fun s ↦ ∃ s1 : Ord(s), ∃ s2 : s ∈ ω, P ⟨⟨s, s1⟩, s2⟩;
  have p := (peano5 A); have hn : ω s⊆ A;
  · apply p; constructor;
    · exact ⟨o0.prop, n0.prop, h0⟩;
    exact fun i ⟨i1, i2, i3⟩ ↦ ⟨(succ i.val).prop, (succ_nat i).prop, h _ i3⟩;
  have hn := hn n.val.val n.prop;
  rcases hn with ⟨_, _, hn⟩; exact hn;

theorem omega_in_K2 : ω ∈ K2 :=
by
  constructor; · exact ω.prop;
  intro h;
  apply @belong_to_self ω.val;
  erw [axiom_of_infinity];
  rw [And.comm]; use h;
  exact omega_subset_K1;

theorem transfinite_induction (A : Class) : A s⊆ On → (∀ α : ordinal, α s⊆ A → α ∈ A) → A = On :=
by
  intros h1 h2;
  apply subseteq_antisymm; · use h1;
  rw [← Class_sub_empty_iff_subseteq];
  by_contra;
  have h3 := axiom_of_regularity_strong this;
  rcases h3 with ⟨x, ⟨h3, h5⟩, h4⟩;
  apply h5;
  apply h2 ⟨x, h3⟩;
  intros a ha;
  erw [← transitive_subset_iff_belong_set On _ On_is_ordinal_class] at h3;
  · erw [← extensionality_belong] at h4;
    have h4 := h4 a;
    erw [has_intersection.proof_intersection] at h4;
    rw [empty_false] at h4; simp only [iff_false, not_and] at h4;
    have h4 := h4 ha;
    erw [not_and_not_right] at h4;
    apply h4; apply h3.1; exact ha;
  exact h3.1;

-- @[elabAsElim]
theorem ordinal.induction {P : ordinal → Prop}
  (α : ordinal)
  (h : ∀ β : ordinal, (∀ γ < β, P γ) → P β)
  : P α :=
by
  have h0 := transfinite_induction (fun x => ∃ h : Ord(x), P ⟨x, h⟩);
  have ha : α ∈ On := α.prop;
    rw [← h0] at ha;
    · rcases ha with ⟨ha_w, ha⟩;
      have haa : α = ⟨α.val, ha_w⟩;
      · apply Subtype.ext; rfl;
      rwa [haa];
  · intro a ⟨h1_w, h1⟩; exact h1_w;
  intros β hb; use β.prop;
  suffices hp : P β;
  · have hbb : β = ⟨β.val, β.prop⟩;
    · apply Subtype.ext; rfl;
    rwa [←hbb];
  apply h; intros γ hg;
  have hb := hb γ.val hg;
  rcases hb with ⟨hb_w, hb⟩;
  have hgg : γ = ⟨γ.val, hb_w⟩;
  · apply Subtype.ext; rfl;
  rwa [hgg];

def trans_rec_class (G : Class) : Class :=
∪(fun f => ∃ β : ordinal, Fnc_on f β.val ∧ ∀ α < β, f[[α.val]] = (G[[f Γ α.val]]))

lemma transfinite_recursion_lemma1 {f g : set} {β γ : ordinal} {G : Class} :
Fnc_on f β.val ∧ (∀ α < β, f[[α.val]] = (G[[f Γ α.val]])) ∧
Fnc_on g γ.val ∧ (∀ α < γ, g[[α.val]] = (G[[g Γ α.val]])) →
∀ α < β, α < γ → (f[[α.val]]) = (g[[α.val]]) :=
by
  intros h δ ha hg;
  apply @ordinal.induction (fun α => α ≤ δ → (f[[α.val]]) = (g[[α.val]]));
  swap; · rfl;
  intros α hb hd;
  rcases h with ⟨h₁, h₂, h₃, h₄⟩;
  rw [h₂]; swap; · apply ord_le_lt_trans hd ha;
  rw [h₄]; swap;
  · apply ord_le_lt_trans;
    assumption';
  congr 1; apply restrict_eq;
    any_goals
      apply Fnc_sub_subseteq;
      apply Fnc_on_sub;;
    assumption';
    any_goals rw [←ord_subseteq]; apply ord_le_trans;;
    · use hd;
  · use ord_lt_le ha;
  · use hd;
  · use ord_lt_le hg;
  intros b h₆;
  have h₇ : Ord(b);
  · apply ord_element_ord' α.val;
    · use α.prop.1;
      use α.prop.2;
    use h₆;
  have hb := hb ⟨b, h₇⟩ h₆;
  apply hb; apply ord_le_trans; · use ord_lt_le h₆;
  assumption;

lemma transfinite_recursion_lemma2 {G : Class}
  {α : set} (hi : ((trans_rec_class G) Γ α).is_set) (hf : Fnc(trans_rec_class G))
  (h : α ∈ D(trans_rec_class G)):
  (trans_rec_class G)[[α]] = G[[((trans_rec_class G) Γ α).to_set hi]] := by
  rw [has_function.proof_domain] at h; rcases h with ⟨y, h⟩;
  rw [value_func _ h]; swap; · exact hf.2;
  unfold trans_rec_class at h; erw [has_union.proof_union] at h;
  rcases h with ⟨c, ⟨h1, ⟨β, ⟨h2, h3⟩⟩⟩⟩;
  have h4 := (@has_function.proof_domain _ _ _ _ c α).2 ⟨y, h1⟩;
  rw [←h2.2] at h4; have h5 := ord_element_ord' β α β.prop h4;
  have h6 := h3 ⟨α, h5⟩ h4; simp only at h6; rw [value_func _ h1] at h6;
  swap; · exact h2.1.2;
  rw [h6]; congr; rw [←extensionality_belong]; intro a;
  rw [Class_to_set_ext, belong_restrict, belong_restrict];
  simp only [and_congr_left_iff, forall_exists_index, and_imp];
  intro x hx z hz; unfold trans_rec_class; erw [has_union.proof_union];
  apply Iff.intro <;> intro hc;
  · use c; use hc; use β;
  rcases hc with ⟨c1, ⟨hc1, ⟨β2, ⟨hb1, hb2⟩⟩⟩⟩;
  have hxo := ord_element_ord' α x h5 hx;
  have hl := transfinite_recursion_lemma1 ⟨h2, h3, hb1, hb2⟩ ⟨x, hxo⟩;
  simp only at hl; have hl1 := @ord_lt_trans ⟨x, hxo⟩ ⟨α, h5⟩ β hx h4;
  rw [hz] at hc1;
  have h7 := (@has_function.proof_domain _ _ _ _ c1 x).2 ⟨z, hc1⟩;
  rw [←hb1.2] at h7; have hl := hl hl1 h7; rw [hz];
  rw [value_func _ hc1] at hl; swap; · exact hb1.1.2;
  unfold_projs at hl1; rw [ord_belong] at hl1;
  rw [h2.2, has_function.proof_domain] at hl1; rcases hl1 with ⟨y2, hy2⟩;
  rw [value_func _ hy2] at hl; · rwa [←hl];
  exact h2.1.2;

theorem transfinite_recursion1 {G : Class} : Fnc_on (trans_rec_class G) On :=
by
  have ff : Fnc(trans_rec_class G); constructor;
  · apply relation_union_is_relation;
    intros x h; rcases h with ⟨α, ⟨⟨⟨h, h₀⟩, h₁⟩, h₂⟩⟩;
    assumption;
  · intros u v w h;
    rcases h with ⟨⟨a, h₀, β, h₁, h₂⟩, b, h₃, γ, h₄, h₅⟩;
    have ha := h₁; have hb := h₄;
    rcases h₁ with ⟨h₁, h₆⟩; rcases h₄ with ⟨h₄, h₇⟩;
    rw [←extensionality_belong] at h₆;
    rw [←extensionality_belong] at h₇;
    have h₆ := (h₆ u).2;
    have h₆ : u ∈ β.val;
    · apply h₆; rw [has_function.proof_domain]; use v;
    have h₇ := (h₇ u).2;
    have h₉ : u ∈ γ.val;
    · apply h₇; rw [has_function.proof_domain]; use w;
    have h₈ : Ord(u);
    · apply ord_element_ord' β.val;
      · use β.prop.1; use β.prop.2;
      use h₆;
    have h₁₀ : v = (↑a[[u]]); · rw [value_func h₁.2 h₀];
    have h₁₁ : w = (↑b[[u]]); · rw [value_func h₄.2 h₃];
    rw [h₁₀, h₁₁];
    have hu : ∃ δ : ordinal, u = δ.val; · use ⟨u, h₈⟩;
    rcases hu with ⟨δ, hu⟩; subst u;
    apply transfinite_recursion_lemma1;
    · use ha;
    · use h₆;
    use h₉;
  have h : Ord(D(trans_rec_class G));
  · apply ordinal_class_transitive;
    · intros x h; rcases h with ⟨y, f, h₀, α, ⟨h₁, h⟩, h₂⟩;
      rw [←extensionality_belong] at h; have h := (h x).2;
      have h : x ∈ α.val;
      · apply h; rw [has_function.proof_domain]; use y;
      exact ord_element_ord' α x α.prop h;
    intros a h x i; rcases h with ⟨y, f, h₀, β, ⟨h₁, h⟩, h₂⟩;
    have ha := β.prop.1;
    use (↑f[[x]]); use f; constructor;
    · apply value_in_func_set;
      · rw [←h]; apply ha; swap; · use i;
        rw [h, has_function.proof_domain]; use y;
      use h₁.2;
    use β; use ⟨h₁, h⟩;
  have h1 := Ord_in_On_or_eq_On _ h;
  cases h1 with
  | inr h1 => rw [←h1]; use ff;
  | inl h1 =>
    exfalso;
    have h2 := class_belong_is_set h1;
    have h : ∃ γ : ordinal, γ.val = D(trans_rec_class G).to_set h2;
    · have h3 := Class_to_set_to_Class h2;
      rw [←h3, ←ord_class] at h;
      use ⟨D(trans_rec_class G).to_set h2, h⟩;
    rcases h with ⟨γ, h⟩;
    have h3 := domain_is_set ff h2;
    let g := ((trans_rec_class G).to_set h3) ∪
      s{s⟨γ.val, (G[[((trans_rec_class G).to_set h3) Γ γ.val]])⟩};
    suffices hg : g s⊆ trans_rec_class G;
    · suffices hh : γ.val ∈ D(trans_rec_class G).to_set h2;
      · rw [h] at hh;
        exact belong_to_self hh;
      rw [Class_to_set_ext];
      have hag : s⟨γ.val, (G[[(trans_rec_class G).to_set h3 Γ γ.val]])⟩ ∈ g;
      · erw [has_binary_union.proof_union]; right; simp;
      have hg := hg _ hag;
      constructor; exact hg;
    intros x hg; erw [has_binary_union.proof_union] at hg;
    cases hg with
    | inl => rwa [←Class_to_set_ext];
    | inr hg =>
      rw [element_in_one_element_set] at hg; subst x;
      use g; constructor;
      · erw [has_binary_union.proof_union]; right; simp;
      have h4 : D((trans_rec_class G).to_set h3) = D(trans_rec_class G).to_set h2;
      · rw [←extensionality_belong]; intro a; rw [Class_to_set_ext];
        rw [has_function.proof_domain, has_function.proof_domain];
        conv => lhs; rhs; ext; rw [Class_to_set_ext];
      have ht : (D((trans_rec_class G).to_set h3) ∩
        D(s{s⟨γ.val, G[[(trans_rec_class G).to_set h3 Γ γ.val]]⟩})) = s0;
      · rw [← function_one_pair.2];
        rw [h4, ←h, ←extensionality_belong]; intro a;
        rw [empty_false];
        simp only [intersection_def, element_in_one_element_set, iff_false, not_and];
        intro h5 h6; rw [h6] at h5;
        exact belong_to_self h5;
      use (succ γ); constructor; constructor;
      · simp only [g];
        apply union_function; constructor;
        · intro x hc; rw [Class_to_set_ext] at hc; exact ff.1 x hc;
        · intro u v w hc; rw [Class_to_set_ext, Class_to_set_ext] at hc;
          exact ff.2 u v w hc;
        · exact function_one_pair.1;
        · rw [ht]; rfl;
      · rw [domain_union, h4, ←h];
        rw [←function_one_pair.2]; unfold succ succ_set;
        erw [←extensionality_belong]; simp;
      intro α ha;
      rw [ord_lt_succ_iff, ord_le] at ha;
      have hd1 := @function_one_pair γ.val (G[[(trans_rec_class G).to_set h3 Γ γ.val]]);
      cases ha with
      | inl ha =>
        have ha2 := ha; unfold_projs at ha2;
        rw [ord_belong, h, Class_to_set_ext] at ha2;
        have he := transfinite_recursion_lemma2 (restrict_is_set ff) ff ha2;
        unfold g;
        rw [union_function_apply_set]; swap;
        · rw [function_to_Class];
          unfold has_belong.to_Class set.to_has_belong id;
          rwa [Class_to_set_to_Class];
        swap; · exact hd1.1;
        swap; · assumption;
        swap; · rw [h4, ←h]; exact ha;
        rw [union_function_restrict hd1.1];
        swap; · rw [ht]; rfl;
        · rw [value_to_Class, Class_to_set_to_Class];
          rw [restrict_to_Class]; swap;
          · rw [Class_to_set_to_Class]; apply restrict_is_set ff;
          rw [he]; congr; rw [Class_to_set_to_Class];
        rw [h4, ←h, subseteq_iff_subset_eq]; left;
        rw [←ord_subset, ←ord_subset_iff_belong]; exact ha;
      | inr ha =>
        rw [ha]; unfold g; rw [binary_union_comm];
        rw [union_function_apply_set hd1.1]; swap;
        · rw [function_to_Class];
          unfold has_belong.to_Class set.to_has_belong id;
          rwa [Class_to_set_to_Class];
        swap; · rwa [intersection_comm];
        swap; · rw [←hd1.2]; simp;
        rw [binary_union_comm];
        rw [union_function_restrict hd1.1, value_one_pair];
        · rw [ht]; rfl;
        rw [h4, ←h];

theorem transfinite_recursion2 {G : Class} {α : ordinal}
{hi : ((trans_rec_class G) Γ α.val).is_set} :
(trans_rec_class G)[[α.val]] = G[[((trans_rec_class G) Γ α.val).to_set hi]] := by
  have h := @transfinite_recursion1 G;
  apply transfinite_recursion_lemma2;
  · apply h.1;
  rw [←h.2]; exact α.prop;

def sup [has_belong α] [has_intersection α Class] [has_union α] (A : α) :=
  ∪(A ∩ On)
def inf [has_belong α] [has_intersection α Class] [has_inter α] (A : α) :=
  ∩(A ∩ On)
def sup_in [has_belong α] [has_intersection α ordinal] [has_union α] (A : α)
  (β : ordinal) := ∪(A ∩ β)
def inf_in [has_belong α] [has_intersection α ordinal] [has_inter α] (A : α)
  (β : ordinal) := ∩(A ∩ β)

def trans_rec_func_h (H : Class) (a : set) : Class :=
  (fun c => ∃ x y, c = s⟨x, y⟩ ∧ (D(x) = s0 ∧ y = a ∨
    ¬D(x) = s0 ∧ D(x) ∈ K1 ∧ y = H[[x[[∪(D(x))]]]] ∨
    D(x) ∈ K2 ∧ y = ∪(W(x))))
theorem trans_rec_func_h_is_func {H : Class} {a : set} : Fnc(trans_rec_func_h H a)
  := by
  constructor;
  · intro c hc; unfold trans_rec_func_h at hc; rw [proof_in_Class] at hc;
    rcases hc with ⟨x, y, h1, h2⟩; rw [h1]; simp;
  intro u v w ⟨h1, h2⟩; unfold trans_rec_func_h at h1 h2;
  rw [proof_in_Class] at h1 h2;
  simp only [ordered_pair_eq_iff, ↓existsAndEq, and_true, exists_eq_left'] at h1 h2;
  cases h1 with
  | inl h1 =>
    rw [h1.1, ←h1.2] at h2;
    simp only [true_and, not_true_eq_false, false_and, false_or] at h2;
    unfold K2 at h2; cases h2 with
    | inl => symm; assumption;
    | inr h2 =>
      rcases h2 with ⟨⟨h2, h3⟩, h4⟩;
      unfold K1 at h3; rw [proof_in_Class] at h3; simp at h3;
      have h4 := o0.prop; contradiction;
  | inr h1 => cases h1 with
    | inl h1 => cases h2 with
      | inl h2 => exfalso; exact h1.1 h2.1;
      | inr h2 => cases h2 with
        | inl h2 => aesop;
        | inr h2 => unfold K2 at h2; exfalso; exact h2.1.2 h1.2.1
    | inr h1 => cases h2 with
      | inl h2 =>
        unfold K2 at h1; rw [h2.1] at h1;
        rcases h1 with ⟨⟨h2, h3⟩, h4⟩;
        unfold K1 at h3; rw [proof_in_Class] at h3; simp at h3;
        have h4 := o0.prop; contradiction;
      | inr h2 => cases h2 with
        | inl h2 => unfold K2 at h1; exfalso; exact h1.1.2 h2.2.1
        | inr h2 => aesop;
def trans_rec_func (H : Class) (a : set) : Class :=
trans_rec_class (trans_rec_func_h H a)
theorem unfold_trans_rec_func_h1 {H : Class} {a : set} (x : set) :
  D(x) = s0 → (trans_rec_func_h H a)[[x]] = a := by
  intro hd; unfold trans_rec_func_h; apply value_func;
  · exact trans_rec_func_h_is_func.2
  rw [proof_in_Class];
  simp only [ordered_pair_eq_iff, ↓existsAndEq, and_true, exists_eq_left'];
  left; assumption;
theorem unfold_trans_rec_func_h2 {H : Class} {a : set} (x : set) :
  ¬D(x) = s0 ∧ D(x) ∈ K1 → (trans_rec_func_h H a)[[x]] = H[[x[[∪(D(x))]]]] := by
  intro hd; unfold trans_rec_func_h; apply value_func;
  · exact trans_rec_func_h_is_func.2
  rw [proof_in_Class];
  simp only [ordered_pair_eq_iff, ↓existsAndEq, and_true, exists_eq_left'];
  right; left; assumption;
theorem unfold_trans_rec_func_h3 {H : Class} {a : set} (x : set) :
  D(x) ∈ K2 → (trans_rec_func_h H a)[[x]] = ∪(W(x)) := by
  intro hd; unfold trans_rec_func_h; apply value_func;
  · exact trans_rec_func_h_is_func.2
  rw [proof_in_Class];
  simp only [ordered_pair_eq_iff, ↓existsAndEq, and_true, exists_eq_left'];
  right; right; assumption;

open Classical in
noncomputable def ordinal_replacement : ordinal → (ordinal → set → Prop) → set :=
  fun α f => make_replacement α.val (fun x y => ∃ h : Ord(x), f ⟨x, h⟩ y)
notation "{" y " // " x " o∈ " a "}" => (ordinal_replacement
  a (fun x _y => _y = y))
theorem ordinal_replacement_axiom (a) (f : ordinal → set → Prop) :
  (∀ u v w, f u v ∧ f u w → v = w) →
  ∀ y : set, y ∈ ordinal_replacement a f ↔ ∃ x, x ∈ a ∧ f x y := by
  intro h y; erw [axiom_of_replacement];
  constructor <;> intro h1 <;> rcases h1 with ⟨x, h1, h2⟩;
  · use ⟨x, ord_element_ord' a x a.prop h1⟩; use h1;
    rcases h2 with ⟨h2, h3⟩; use h3;
  · use x.val; use h1; use x.prop; use h2;
  intro u v w ⟨ h1, h2⟩; apply h; use h1.2; use h2.2;
noncomputable def ordinal_replacement2 : ordinal →
  (ordinal → ordinal → Prop) → set :=
  fun α f => make_replacement α.val (fun x y => ∃ h : Ord(x), ∃ h2 : Ord(y),
    f ⟨x, h⟩ ⟨y, h2⟩)
theorem ordinal_replacement_axiom2 (a) (f : ordinal → ordinal → Prop) :
  (∀ u v w, f u v ∧ f u w → v = w) →
  ∀ y : set, y ∈ ordinal_replacement2 a f ↔ ∃ x y2, x ∈ a ∧ f x y2 ∧ y2.val = y := by
  intro h y; erw [axiom_of_replacement];
  constructor <;> intro h1 <;> rcases h1 with ⟨x, h1, h2⟩;
  · use ⟨x, ord_element_ord' a x a.prop h1⟩;
    rcases h2 with ⟨h2, hy, h3⟩; use ⟨y, hy⟩; use h1;
  · use x.val; use h2.1; use x.prop; rw [←h2.2.2]; use h1.prop; use h2.2.1
  intro u v w ⟨h1, h2⟩; have h := h _ _ _ ⟨h1.2.2, h2.2.2⟩;
  exact Subtype.coe_inj.2 h;
theorem ordinal_replacement_axiom3 (a) (f : ordinal → ordinal → Prop) :
  (∀ u v w, f u v ∧ f u w → v = w) →
  ∀ y : ordinal, y ∈ ordinal_replacement2 a f ↔ ∃ x y2, x ∈ a ∧ f x y2 ∧ y2 = y := by
  intro h y; erw [axiom_of_replacement];
  constructor <;> intro h1 <;> rcases h1 with ⟨x, h1, h2⟩;
  · use ⟨x, ord_element_ord' a x a.prop h1⟩;
    rcases h2 with ⟨h2, hy, h3⟩; use y; use h1; use h3;
  · use x.val; use h2.1; use x.prop; rw [←h2.2.2]; use h1.prop; use h2.2.1
  intro u v w ⟨h1, h2⟩; have h := h _ _ _ ⟨h1.2.2, h2.2.2⟩;
  exact Subtype.coe_inj.2 h;
noncomputable def ordinal_function_union (a : ordinal) (f : ordinal → ordinal)
  : ordinal :=
  ⟨∪(ordinal_replacement2 a (fun x _y => _y = f x)), by
    apply ord_class_union_ordinal; intro x h;
    have h2 : ∀ (u v w : ordinal), v = f u ∧ w = f u → v = w;
    · intros; aesop;
    have h1 := (ordinal_replacement_axiom2 a (fun x _y ↦ _y = f x) h2 x).1 h;
    rcases h1 with ⟨x1, y2, h1⟩; rw [←h1.2.2]; exact y2.prop;
  ⟩
notation "⋃(" x " oo∈ " a ", " y ")" => ordinal_function_union a (fun x => y)
theorem ordinal_union_axiom (β) (f : ordinal → ordinal) :
  ∪({(f γ).val // γ o∈ β}) = ⋃(γ oo∈ β, f γ).val := by
  unfold ordinal_function_union; simp only; congr;
  rw [←extensionality_belong]; intro a;
  rw [ordinal_replacement_axiom, ordinal_replacement_axiom2];
  · simp only [↓existsAndEq, true_and];
    conv => lhs; rhs; ext; rhs; rw [Eq.comm];
  all_goals intros; aesop;
theorem trans_func_rec1 {H : Class} {a : set} : (trans_rec_func H a)[[s0]] = a := by
  unfold trans_rec_func; rw [←o0_eq_s0];
  rw [transfinite_recursion2]; swap;
  · exact restrict_is_set transfinite_recursion1.1;
  apply unfold_trans_rec_func_h1; rw [o0_eq_s0];
  conv => lhs; congr; lhs; rw [restrict_empty transfinite_recursion1.1];
  rw [set_to_Class_to_set, ←extensionality_belong]; intro a;
  rw [has_function.proof_domain]; simp [empty_false];
theorem trans_func_rec2 {H : Class} {a : set} {β : ordinal} :
  (trans_rec_func H a)[[(succ β).val]] = H[[(trans_rec_func H a)[[β.val]]]] := by
  have hc : has_belong.to_Class (succ β).val s⊆ On;
  · intro x h; exact ord_element_ord' _ x (succ β).prop h;
  unfold trans_rec_func; rw [transfinite_recursion2]; swap;
  · exact restrict_is_set transfinite_recursion1.1;
  rw [unfold_trans_rec_func_h2];
  conv =>
    lhs; rhs; rhs; congr; rw [class_to_set_domain]; lhs; rw [domain_restrict];
    rw [←transfinite_recursion1.2, intersection_to_class_has_belong];
    rw [intersection_comm, ←subseteq_iff_eq_intersection.1 hc];
  conv =>
    lhs; rhs; rw [set_to_Class_to_set_has_belong, union_succ_set];
  · congr 1; rw [value_to_Class, Class_to_set_to_Class];
    apply restrict_value; exact self_belong_succ;
  rw [class_to_set_domain];
  conv =>
    lhs; rhs; lhs; lhs; rw [domain_restrict];
    rw [←transfinite_recursion1.2, intersection_to_class_has_belong];
    rw [intersection_comm, ←subseteq_iff_eq_intersection.1 hc];
  conv =>
    lhs; rhs; rw [set_to_Class_to_set_has_belong];
  conv =>
    rhs; lhs; lhs; rw [domain_restrict];
    rw [←transfinite_recursion1.2,intersection_to_class_has_belong];
    rw [intersection_comm, ←subseteq_iff_eq_intersection.1 hc];
  conv => rhs; lhs; rw [set_to_Class_to_set_has_belong];
  constructor;
  · intro h; apply empty_false.1; · rw [←h]; exact self_belong_succ;
  unfold K1; constructor;
  · right; use β; rfl;
theorem trans_func_rec3 {H : Class} {a : set} {β : ordinal} (h : β ∈ K2) :
  (trans_rec_func H a)[[β.val]] = ∪({(trans_rec_func H a)[[γ.val]] // γ o∈ β}) := by
  unfold trans_rec_func;
  rw [transfinite_recursion2]; swap;
  · exact restrict_is_set transfinite_recursion1.1;
  rw [unfold_trans_rec_func_h3];
  · congr; rw [←extensionality_belong]; intro x;
    rw [has_function.proof_range];
    rw [ordinal_replacement_axiom];
    conv =>
      lhs; rhs; ext; rw [set_belong_to_class, Class_to_set_to_Class_has_belong];
      rw [pair_in_restrict, And.comm]; rhs;
    constructor <;> intro h1 <;> rcases h1 with ⟨x1, h1, h2⟩;
    · use ⟨x1, ord_element_ord' β x1 β.prop h1⟩; use h1;
      · symm; apply value_func transfinite_recursion1.1.2; assumption;
    · use x1.val; use h1;
      rw [h2]; apply value_func2 transfinite_recursion1.1.2;
      rw [←transfinite_recursion1.2];
      exact ord_element_ord' β.val x1.val β.prop h1;
    intro u v w ⟨h1, h2⟩; aesop;
  have hc : has_belong.to_Class β.val s⊆ On;
  · intro x h; exact ord_element_ord' _ x β.prop h;
  conv =>
    lhs; rw [class_to_set_domain]; lhs; rw [domain_restrict];
    rw [←transfinite_recursion1.2, intersection_to_class_has_belong, intersection_comm];
    rw [←subseteq_iff_eq_intersection.1 hc];
  rw [set_to_Class_to_set_has_belong]; exact h;

syntax "∀ " ident " o∈ " term ", " term : term
syntax "∀ " "_" " o∈ " term ", " term : term
macro_rules
| `(∀ $x:ident o∈ $A, $P) =>
    `(∀ $x:ident : ordinal, $x ∈ $A → $P)
| `(∀ _ o∈ $A, $P) =>
    `(∀ x : ordinal, x ∈ $A → $P)
syntax "∃ " ident " o∈ " term ", " term : term
syntax "∃ " "_" " o∈ " term ", " term : term
macro_rules
| `(∃ $x:ident o∈ $A, $P) =>
    `(∃ $x:ident : ordinal, $x ∈ $A ∧ $P)
| `(∃ _ o∈ $A, $P) =>
    `(∃ x : ordinal, x ∈ $A ∧ $P)

theorem ordinal_union_lt {α β : ordinal} {f : ordinal → ordinal} :
  α < ⋃(γ oo∈ β, f γ) ↔ ∃ γ o∈ β, α < f γ := by
  have h : ∀ (u v w : ordinal), v = f u ∧ w = f u → v = w;
  · simp only [and_imp, forall_eq_apply_imp_iff, imp_self, implies_true];
  conv =>
    lhs; unfold ordinal_function_union; unfold LT.lt ordinal.to_has_lt id;
    erw [ord_belong]; simp only;
    erw [has_union.proof_union]; rhs; ext; rw [And.comm]; lhs;
    rw [ordinal_replacement_axiom2 _ _ h]; simp only [↓existsAndEq, true_and];
  simp only [↓existsAndEq, and_true]; rfl;
theorem ordinal_union_set {α : set} {β : ordinal} {f : ordinal → ordinal} :
  α ∈ ⋃(γ oo∈ β, f γ) ↔ ∃ γ o∈ β, α ∈ f γ := by
  have h : ∀ (u v w : ordinal), v = f u ∧ w = f u → v = w;
  · simp only [and_imp, forall_eq_apply_imp_iff, imp_self, implies_true];
  conv =>
    lhs; unfold ordinal_function_union; unfold LT.lt ordinal.to_has_lt id;
    erw [set_ord_belong]; simp only;
    erw [has_union.proof_union]; rhs; ext; rw [And.comm]; lhs;
    rw [ordinal_replacement_axiom2 _ _ h]; simp only [↓existsAndEq, true_and];
  simp only [↓existsAndEq, and_true]; rfl;

theorem ordinal_set_replace {β : ordinal} {f g : ordinal → ordinal} :
  (∀ γ o∈ β, f γ = g γ) → {(f γ).val // γ o∈ β} = {(g γ).val // γ o∈ β} := by
  intro h; rw [←extensionality_belong]; intro a;
  rw [ordinal_replacement_axiom, ordinal_replacement_axiom];
  · apply exists_congr; simp only [and_congr_right_iff]; intro b hb; rw [h b hb];
  all_goals simp only [and_imp, forall_eq_apply_imp_iff, imp_self, implies_true];
theorem ordinal_union_replace {β : ordinal} {f g : ordinal → ordinal} :
  (∀ γ o∈ β, f γ = g γ) → ⋃(γ oo∈ β, f γ) = ⋃(γ oo∈ β, g γ) := by
  intro h; apply Subtype.ext; rw [←ordinal_union_axiom, ←ordinal_union_axiom];
  congr 1; exact ordinal_set_replace h;

theorem ordinal_replacement_id {β} : {γ.val // γ o∈ β} = β.val := by
  rw [←extensionality_belong]; intro a; rw [ordinal_replacement_axiom];
  constructor <;> intro hx;
  · rcases hx with ⟨x, h1, h2⟩; rw [h2]; exact h1;
  · use ⟨a, ord_element_ord' β a β.prop hx⟩; use hx;
  intros; aesop;

theorem ord_k2_succ_in {α β : ordinal} (h : α ∈ K2) :
  β ∈ α → succ β ∈ α := by
  intro hb; erw [ord_in_k2] at h; push Not at h;
  have hn := h.2 β; cases ord_succ_belong hb with
  | inl => symm at hn; contradiction;
  | inr => assumption;

theorem ord_k2_union_eq_self {α : ordinal} (h : α ∈ K2) : ∪(α.val) = α.val := by
  rw [←extensionality_belong]; intro a; erw [has_union.proof_union];
  constructor <;> intro h1;
  · rcases h1 with ⟨c, h1, h2⟩; exact α.prop.1 c h2 a h1;
  have ha := ord_element_ord' α a α.prop h1;
  use succ_set a; use self_belong_succ; exact @ord_k2_succ_in α ⟨a, ha⟩ h h1;

theorem ord_union_val {α : ordinal} : ∪(α).val = ∪(α).val := by rfl

theorem ord_union_le_sup {β : ordinal} {f : ordinal → ordinal} :
  ∀ α o∈ β, f α ≤ ⋃(γ oo∈ β, f γ) := by
  intro α ha x hx;
  unfold belong has_belonged_to.belonged_to set.to_has_belonged_to id;
  unfold set.belonged_to has_belong.belong ordinal.to_has_belong id;
  simp only; erw [←ordinal_union_axiom, has_union.proof_union];
  use (f α).val; use hx; rw [ordinal_replacement_axiom]; · use α;
  simp only [and_imp, forall_eq_apply_imp_iff, imp_self, implies_true];

theorem ord_union_sup_le {β M : ordinal} {f : ordinal → ordinal} :
  (∀ α o∈ β, f α ≤ M) → ⋃(γ oo∈ β, f γ) ≤ M := by
  intro h x hx;
  erw [set_ord_belong, ←ordinal_union_axiom, has_union.proof_union] at hx;
  rcases hx with ⟨c, h3, hx⟩;
  rw [ordinal_replacement_axiom] at hx;
  · rcases hx with ⟨y, h4, hx⟩; subst c;
    exact h y h4 x h3;
  simp only [and_imp, forall_eq_apply_imp_iff, imp_self, implies_true];

theorem ord_ge_0 {α : ordinal} : o0 ≤ α := by
  intro x; erw [empty_false]; simp only [IsEmpty.forall_iff];
theorem ord_ne_0_gt {α : ordinal} : ¬α = o0 → o0 < α := by
  intro h;
  cases ord_le.1 (@ord_ge_0 α) with
  | inl => assumption;
  | inr => subst α; contradiction;
theorem ord_ne_0_gt_iff {α : ordinal} : ¬α = o0 ↔ o0 < α := by
  use ord_ne_0_gt; intro h1 h2; subst α; exact belong_to_self h1;

theorem minimal_ordinal {f : ordinal → Prop} :
  (∃ α, f α) → ∃ β, f β ∧ ∀ γ, f γ → β ≤ γ := by
  intro ⟨α, h⟩; by_contra ht; push Not at ht;
  conv at ht => ext; rhs; rhs; ext; rhs; rw [ord_nle];
  have g := @ordinal.induction (fun γ => ¬(f γ)) α;
  have ht := fun β => mt (ht β);
  conv at ht => ext; lhs; push Not; rhs; rw [Iff.intro Function.swap Function.swap];
  exact g ht h;

theorem ord_k2_gt_0 {α : ordinal} (h : α ∈ K2) : o0 < α := by
  erw [ord_in_k2, Eq.comm] at h;
  exact ord_lt.2 ⟨ord_ge_0, h.1⟩;

theorem nat_induction (A : ordinal → Prop) : A o0 →
  (∀ i o∈ ω, A i → A (succ i)) → (∀ i o∈ ω, A i) := by
  have h := peano5 (fun s => ∃ ho : Ord(s), A ⟨s, ho⟩);
  simp only [and_imp] at h; rw [proof_in_Class] at h;
  intro h1 h2; have h := h ⟨o0.prop, h1⟩;
  conv at h => lhs; ext; rw [proof_in_Class, proof_in_Class];
  conv at h => rhs; unfold subseteq; rhs; rw [proof_in_Class];
  have h := h (fun i j => ⟨ord_element_ord _ _ (ord_k2_succ_in omega_in_K2 i.prop),
      h2 i.val i.prop j.2⟩);
  intro i hi; rcases h i.val hi with ⟨ho, h⟩;
  have h3 : i = ⟨i.val, ho⟩; · exact Subtype.ext rfl;
  rwa [h3];

theorem omega_recursion {H : Class} {a : set} :
  ∃!f : set, (Fnc_on f ω.val) ∧ f[[o0.val]] = a ∧
  ∀ m o∈ ω, f[[(succ m).val]] = H[[f[[m.val]]]] := by
  use ((trans_rec_func H a) Γ ω.val).to_set
    (restrict_is_set transfinite_recursion1.1);
  constructor <;> simp only [and_imp];
  · constructor;
    · constructor;
      · rw [class_to_set_func]; exact restrict_is_func transfinite_recursion1.1;
      rw [class_to_set_domain];
      have h : ω.val s⊆ On;
      · intro x hx; exact ord_element_ord _ _ hx;
      have h : On ∩ ω.val = ω.val.to_Class;
      · rw [←extensionality_belong]; intro a; rw [set_belong_set_to_class2];
        simp only [intersection_def, and_iff_right_iff_imp]; exact h a;
      conv =>
        rhs; lhs; rw [domain_restrict]; unfold trans_rec_func;
        rw [←transfinite_recursion1.2, h];
      symm; exact set_to_Class_to_set _;
    constructor;
    · rw [value_to_Class, Class_to_set_to_Class, restrict_value];
      · exact trans_func_rec1;
      exact ord_k2_gt_0 omega_in_K2;
    intro m hm; rw [value_to_Class, Class_to_set_to_Class, restrict_value];
    · rw [value_to_Class, Class_to_set_to_Class, restrict_value];
      · exact trans_func_rec2;
      exact hm;
    exact ord_k2_succ_in omega_in_K2 hm;
  intro y h1 h2 h3; rw [←extensionality_belong]; intro c;
  rw [Class_to_set_ext, belong_restrict];
  have h4 := h1.1.1 c; rw [has_product.proof_product] at h4;
  simp only [set_in_allset, true_and] at h4;
  have h5 := nat_induction (fun m =>
    ∀ n, s⟨m.val, n⟩ ∈ y ↔ s⟨m.val, n⟩ ∈ trans_rec_func H a);
  have h6 : (∀ (n : set), s⟨s0, n⟩ ∈ y ↔ s⟨s0, n⟩ ∈ trans_rec_func H a);
  · intro n; unfold trans_rec_func;
    rw [value_func_iff h1.1.2, value_func_iff transfinite_recursion1.1.2];
    rw [o0_eq_s0] at h2;
    rw [←trans_rec_func, trans_func_rec1, h2]; simp only [and_congr_right_iff];
    intro; unfold trans_rec_func;
    rw [←h1.2, ←transfinite_recursion1.2]; have h : s0 ∈ On := o0.prop;
    simp only [h, iff_true];
    exact ord_k2_gt_0 omega_in_K2;
  have h5 := h5 h6; have h6 : ∀ (i : ordinal), i ∈ ω →
    ∀ (n : set), s⟨i.val, n⟩ ∈ y ↔ s⟨i.val, n⟩ ∈ trans_rec_func H a;
  · apply h5; intro i hi1 hi2 n; unfold trans_rec_func;
    rw [value_func_iff h1.1.2, value_func_iff transfinite_recursion1.1.2];
    conv at hi2 =>
      ext; unfold trans_rec_func;
      rw [value_func_iff h1.1.2, value_func_iff transfinite_recursion1.1.2];
    have hi2 := hi2 (y[[i.val]]); simp only [true_and] at hi2;
    rw [←h1.2, ←transfinite_recursion1.2] at *;
    simp only [ord_belong.1 hi1, true_iff] at hi2;
    have h3 := h3 i hi1; rw [←hi2.1, ←trans_rec_func] at h3;
    rw [←trans_func_rec2] at h3; unfold trans_rec_func at h3; rw [←h3];
    simp only [and_congr_right_iff]; intro;
    simp only [ord_belong.1 (ord_k2_succ_in omega_in_K2 hi1), true_iff];
    exact (succ i).prop;
  constructor <;> intro h0;
  · rcases h4 h0 with ⟨m, n, h4⟩; subst c;
    simp only [ordered_pair_eq_iff, exists_and_left,
      ↓existsAndEq, and_true, exists_eq_right'];
    have h4 := h1.2; have h5 := (has_function.proof_domain _).2 ⟨_, h0⟩;
    rw [←h4] at h5; symm; use h5;
    exact (h6 ⟨m, ord_element_ord _ _ h5⟩ h5 n).1 h0;
  rcases h0 with ⟨h0, m, h5, n, _⟩; subst c;
  exact (h6 ⟨m, ord_element_ord _ _ h5⟩ h5 n).2 h0;

theorem rec_choose1 [has_belong α] {A : α} {G : Class}
  (h0 : ∀ α : ordinal, (trans_rec_class G Γ α).is_set)
  (h : ∀ α : ordinal, G[[(trans_rec_class G Γ α).to_set (h0 α)]] ∈
  (has_belong.to_Class A) - (trans_rec_class G)[α]) :
  W(trans_rec_class G) s⊆ A := by
  intro c; rw [has_function.proof_range]; intro ⟨x, hc⟩;
  have f1 := @transfinite_recursion1 G;
  have f2 := fun α ↦ @transfinite_recursion2 G α (restrict_is_set f1.1);
  have h3 := (has_function.proof_domain _).2 ⟨_, hc⟩;
  rw [←f1.2] at h3; let x : ordinal := ⟨x, h3⟩;
  have h4 := value_func f1.1.2 hc;
  have f3 := f2 x; rw [h4] at f3; rw [f3, set_belong_to_class];
  exact (h _).1;
theorem rec_choose2 [has_belong α] {A : α} {G : Class}
  (h0 : ∀ α : ordinal, (trans_rec_class G Γ α).is_set)
  (h : ∀ α : ordinal, G[[(trans_rec_class G Γ α).to_set (h0 α)]] ∈
  (has_belong.to_Class A) - (trans_rec_class G)[α]) :
  Un₂(trans_rec_class G) := by
  have f1 := @transfinite_recursion1 G;
  have f2 := fun α ↦ @transfinite_recursion2 G α (restrict_is_set f1.1);
  use f1.1.2;
  suffices h1 : ∀ v w : ordinal, v < w →
    trans_rec_class G[[v.val]] ≠ trans_rec_class G[[w.val]];
  · intro u v w ⟨hu, hv⟩; rw [pair_in_inverse] at hu hv;
    have hu1 := (has_function.proof_domain _).2 ⟨_, hu⟩;
    have hv1 := (has_function.proof_domain _).2 ⟨_, hv⟩;
    rw [←f1.2] at hu1 hv1;
    let v : ordinal := ⟨v, hu1⟩; let w : ordinal := ⟨w, hv1⟩;
    suffices hw : v = w; · exact Subtype.coe_inj.2 hw;
    have hu2 := value_func f1.1.2 hu;
    have hv2 := value_func f1.1.2 hv;
    rw [←hv2] at hu2;
    cases @ord_total v w with
    | inl hu3 => exfalso; exact h1 _ _ hu3 hu2;
    | inr hu3 => cases hu3 with
      | inl => assumption;
      | inr hu3 => symm at hu2; exfalso; exact h1 _ _ hu3 hu2;
  intro v w hu hv;
  have hu2 : trans_rec_class G[[v.val]] ∈ (trans_rec_class G)[w.val];
  · rw [has_function.proof_range]; use v.val; rw [pair_in_restrict];
    have hv2 : v.val ∈ On := v.prop;
    rw [f1.2] at hv2; use value_func2 f1.1.2 hv2; exact hu;
  have hv2 := f2 w; rw [hv, hv2] at hu2;
  have hu3 := (@class_is_set_range (trans_rec_class G Γ w.val)
    (restrict_is_set f1.1));
  rw [←Class_to_set_ext hu3, ←@class_to_set_range _ (restrict_is_set f1.1)] at hu2;
  rw [class_to_set_range, Class_to_set_ext] at hu2;
  exact (h _).2 hu2;
theorem rec_choose3 {A : Class} {G : Class}
  (h0 : ∀ α : ordinal, (trans_rec_class G Γ α).is_set)
  (h : ∀ α : ordinal, G[[(trans_rec_class G Γ α).to_set (h0 α)]] ∈
  (has_belong.to_Class A) - (trans_rec_class G)[α]) : Class.is_proper A := by
  have f1 := @transfinite_recursion1 G;
  have f2 := fun α ↦ @transfinite_recursion2 G α (restrict_is_set f1.1);
  intro a; have h1 : W(trans_rec_class G) s⊆ A.to_set a;
  · intro c; rw [has_function.proof_range]; intro ⟨x, h2⟩;
    have h3 := value_func f1.1.2 h2; subst h3;
    have h4 := (has_function.proof_domain _).2 ⟨_, h2⟩;
    rw [←f1.2] at h4; rw [f2 ⟨x, h4⟩, Class_to_set_ext];
    exact (h _).1;
  have h2 := subseteq_is_set h1;
  have un2 := rec_choose2 h0 h; rw [←domain_inv] at h2;
  have h3 := domain_is_set ⟨inverse_is_relation, un2.2⟩ h2;
  have h3 := (@class_is_set_range _ h3);
  rw [range_inv, ←f1.2] at h3; exact On_proper_class h3;

theorem rec_choose_set {A : set} {G : Class}
  (h0 : ∀ α : ordinal, (trans_rec_class G Γ α).is_set)
  (h : ∀ α : ordinal, A - (trans_rec_class G)[α] ≠ s0 →
  G[[(trans_rec_class G Γ α).to_set (h0 α)]] ∈
  A - (trans_rec_class G)[α]) :
  ∃ α : ordinal, (∀ β o∈ α, A.to_Class - (trans_rec_class G)[β] ≠ s0)
  ∧ (trans_rec_class G)[α] = A ∧ Un₂((trans_rec_class G) Γ α) := by
  have f1 := @transfinite_recursion1 G;
  have f2 := fun α ↦ @transfinite_recursion2 G α (restrict_is_set f1.1);
  have ha : ∃ α : ordinal, A - (trans_rec_class G)[α] = s0;
  · by_contra ha; push Not at ha;
    have h1 := fun α ↦ h α (ha α);
    have ha1 := rec_choose3 h0 h1; exact ha1 (set_to_Class_is_set);
  rcases minimal_ordinal ha with ⟨α, ha1, ha2⟩; use α;
  have ha2 := fun β ↦ mt (ha2 β);
  conv at ha2 => rhs; lhs; rw [ord_nle];
  use ha2; constructor;
  · apply subseteq_antisymm;
    · intro c; rw [has_function.proof_range]; intro ⟨x, hc⟩;
      rw [pair_in_restrict] at hc; rcases hc with ⟨hc1, hc2⟩;
      rw [←set_belong_set_to_class];
      have ho := (has_function.proof_domain _).2 ⟨_, hc1⟩;
      rw [←f1.2] at ho; let x : ordinal := ⟨x, ho⟩;
      have ha2 := ha2 x hc2; have ha3 := h _ ha2;
      have hc3 := value_func f1.1.2 hc1;
      have ha4 := f2 x; rw [←hc3, ha4, set_belong_set_to_class];
      exact ha3.1;
    intro x hx; by_contra hx2; have hx := And.intro hx hx2;
    rw [←class_sub_is_sub] at hx; rw [ha1, ←set_belong_set_to_class] at hx;
    exact empty_false.1 hx;
  constructor; · exact (restrict_is_func f1.1).2;
  intro u;
  suffices hu : ∀ (v w : ordinal), v < w → ¬(s⟨u, v.val⟩ ∈ (trans_rec_class G Γ α)⁻¹ ∧
    s⟨u, w.val⟩ ∈ (trans_rec_class G Γ α)⁻¹);
  · intro v w ⟨hv, hw⟩; have hv' := hv; have hw' := hw;
    rw [pair_in_inverse, pair_in_restrict] at hv hw;
    rcases hv with ⟨hv1, hv2⟩; rcases hw with ⟨hw1, hw2⟩;
    let v : ordinal := ⟨v, ord_element_ord _ _ hv2⟩;
    let w : ordinal := ⟨w, ord_element_ord _ _ hw2⟩;
    cases @ord_total v w with
    | inl ha3 => exfalso; exact hu _ _ ha3 ⟨hv', hw'⟩;
    | inr ha3 => cases ha3 with
      | inl ha3 => exact Subtype.coe_inj.2 ha3;
      | inr ha3 => exfalso; exact hu _ _ ha3 ⟨hw', hv'⟩;
  intro v w hu ⟨hv, hw⟩;
  rw [pair_in_inverse, pair_in_restrict] at hv hw;
  rcases hv with ⟨hv1, hv2⟩; rcases hw with ⟨hw1, hw2⟩;
  have hv3 := value_func f1.1.2 hv1; have hw3 := value_func f1.1.2 hw1;
  have hu2 : u ∈ (trans_rec_class G)[w.val];
  · rw [has_function.proof_range]; use v.val; rw [pair_in_restrict];
    use hv1; use hu;
  have hu3 := h w (ha2 _ hw2);
  have hu4 : (trans_rec_class G Γ w) = (trans_rec_class G Γ w.val) := rfl;
  conv at hu3 => lhs; rhs; lhs; rw [hu4];
  rw [←f2 w, hw3] at hu3; exact hu3.2 hu2;

theorem E_well_order_ord (α : ordinal) : is_well_order E α.val := by
  use E_foundational; intro x hx y hy; simp only [E_simp];
  let x : ordinal := ⟨x, ord_element_ord _ _ hx⟩;
  let y : ordinal := ⟨y, ord_element_ord _ _ hy⟩;
  have h := @ord_total x y;
  cases h with
  | inl => left; assumption;
  | inr h => cases h with
    | inl h => right; left; exact (@Subtype.coe_inj _ _ x y).2 h;
    | inr h => right; right; assumption;
theorem E_well_order_ord_class [has_belong α] [has_intersection α Class]
  {A : α} (h : A s⊆ On) : is_well_order E A := by
  use E_foundational; intro x hx y hy; simp only [E_simp];
  let x : ordinal := ⟨x, h _ hx⟩;
  let y : ordinal := ⟨y, h _ hy⟩;
  have h := @ord_total x y;
  cases h with
  | inl => left; assumption;
  | inr h => cases h with
    | inl h => right; left; exact (@Subtype.coe_inj _ _ x y).2 h;
    | inr h => right; right; assumption;

theorem th7_45 {R A B : Class} (h1 : is_well_founded_well_order R A) (h2 : B s⊆ A)
  (h3 : ∀ x s∈ A, ∀ y s∈ B, R& x y → x ∈ B) : A = B ∨ ∃ x s∈ A, B = A ∩ R⁻¹[s{x}] := by
  rw [or_iff_not_imp_left]; intro h4; rw [←extensionality_belong] at h4; push Not at h4;
  rcases h4 with ⟨a, h4⟩; have h21 := or_not_of_imp (h2 a);
  rw [or_iff_not_and_not, not_not] at h21; rw [Or.comm, or_iff_not_imp_left] at h4;
  have h4 := h4 h21; have h5 : A - B ≠ s0;
  · rw [nonempty_class_iff_has_element]; exact ⟨a, h4⟩;
  have h6 := wfwo_class_minimal h1 (fun x ↦ And.left) h5;
  rcases h6 with ⟨b, h61, h62⟩;
  have h7 : ∀ x s∈ B, R& x b;
  · intro x hx; cases h1.2.2 x (h2 _ hx) b h61.1 with
    | inl => assumption;
    | inr hx1 => cases hx1 with
      | inl => subst x; exfalso; exact h61.2 hx;
      | inr hx1 => exfalso; exact h61.2 (h3 b h61.1 x hx hx1);
  use b; use h61.1; apply subseteq_antisymm <;> intro x hx;
  · use h2 x hx; rw [has_function.proof_range];
    conv => rhs; ext; simp only [pair_in_restrict, element_in_one_element_set,
      pair_in_inverse];
    simp only [↓existsAndEq, and_true]; exact h7 x hx;
  simp only [intersection_def, has_function.proof_range, pair_in_restrict,
    element_in_one_element_set, pair_in_inverse, ↓existsAndEq, and_true] at hx;
  by_contra hx1; have hx1 := And.intro hx.1 hx1; rw [well_found_eqv_class] at h62;
  simp only at h62; exact h62 x hx1 hx.2;
theorem th7_481 [has_belong α] [has_intersection α Class] [has_function α]
  [has_intersection set α] [has_intersection Class α]
  {R : α} {A G : Class}
  (h2 : is_well_founded_well_order R A)
  (hg : G = fun c ↦ ∃ x y, c = s⟨x, y⟩ ∧ y ∈ A - W(x) ∧
    (A - W(x)) ∩ R⁻¹[s{y}] = s0) : Fnc(G) := by
  · constructor;
    · intro c hc; rw [hg, proof_in_Class] at hc; rcases hc with ⟨_, _, _, _⟩;
      subst c; simp;
    intro u v w ⟨hv, hw⟩; rw [hg, proof_in_Class] at hv hw;
    simp only [ordered_pair_eq_iff, ↓existsAndEq, and_true,
      exists_eq_left'] at hv hw;
    rw [well_found_eqv_class] at hv hw;
    have hv1 := hv.2 w hw.1; have hw1 := hw.2 v hv.1; simp at hv1 hw1;
    have hv2 := hv.1.1; have hw2 := hw.1.1; have h3 := h2.2.2 _ hv2 _ hw2;
    cases h3 with
    | inl => contradiction;
    | inr h3 => cases h3 with
      | inl => assumption;
      | inr => contradiction;
theorem th7_482 [has_belong α] [has_intersection α Class] [has_function α]
  [has_intersection set α] [has_intersection Class α]
  {R : α} {A G : Class}
  (h2 : is_well_founded_well_order R A)
  (hg : G = fun c ↦ ∃ x y, c = s⟨x, y⟩ ∧ y ∈ A - W(x) ∧
    (A - W(x)) ∩ R⁻¹[s{y}] = s0) : ∀ x : set, A - W(x) ≠ s0
    → G[[x]] ∈ (A - W(x)) ∧ (A - W(x)) ∩ R⁻¹[s{G[[x]]}] = s0 := by
  have hg1 := th7_481 h2 hg;
  intro x hx;
  have h6 := wfwo_class_minimal h2 (fun x ↦ And.left) hx;
  conv at h6 => rhs; ext; rw [proof_in_Class];
  rcases h6 with ⟨x2, h61, h62⟩;
  have hx1 : s⟨x, x2⟩ ∈ G;
  · conv => rhs; rw [hg];
    rw [proof_in_Class]; simp only [ordered_pair_eq_iff, ↓existsAndEq,
      and_true, exists_eq_left']; exact ⟨h61, h62⟩;
  have hx2 := value_func hg1.2 hx1; rw [hx2]; exact ⟨h61, h62⟩;
theorem ord_isom_wfwo_class {A R G : Class} (h1 : ¬A.is_set)
  (h2 : is_well_founded_well_order R A)
  (hg : G = fun c ↦ ∃ x y, c = s⟨x, y⟩ ∧ y ∈ A - W(x) ∧
    (A - W(x)) ∩ R⁻¹[s{y}] = s0) : Isom (trans_rec_class G) E R On A := by
  have f1 := @transfinite_recursion1 G;
  have f2 := fun α ↦ @transfinite_recursion2 G α (restrict_is_set f1.1);
  have hg1 := th7_481 h2 hg;
  have h4 := well_order_minimal h2.2;
  have h5 : ∀ α : ordinal, A - (trans_rec_class G)[α.val] ≠ s0;
  · by_contra ht; push Not at ht; apply h1; rcases ht with ⟨α, ht⟩;
    rw [Class_sub_empty_iff_subseteq] at ht; apply subseteq_is_set;
    · intro x hx;
      have ht := ht _ hx; rw [←Class_to_set_ext (@class_is_set_range _
        (restrict_is_set f1.1))] at ht; use ht;
  have h6 := fun α ↦ wfwo_class_minimal h2 (fun x ↦ And.left) (h5 α);
  conv at h6 => ext; rhs; ext; rw [proof_in_Class];
  have h6t : ∀ α : ordinal, (trans_rec_class G)[α.val] =
    W((trans_rec_class G Γ α.val).to_set (restrict_is_set f1.1)).to_Class;
  · intro α; rw [class_to_set_range, Class_to_set_to_Class];
  have hx : ∀ α : ordinal, G[[(trans_rec_class G Γ α.val).to_set
    (restrict_is_set f1.1)]] ∈ A - (trans_rec_class G)[α.val] ∧
    (A - (trans_rec_class G)[α.val]) ∩ R⁻¹[s{G[[(trans_rec_class G Γ α.val).to_set
    (restrict_is_set f1.1)]]}] = s0;
  · intro α; rcases h6 α with ⟨x, h61, h62⟩;
    rw [h6t] at h61 h62;
    have hx1 : s⟨(trans_rec_class G Γ α.val).to_set (restrict_is_set f1.1), x⟩ ∈ G;
    · conv => rhs; rw [hg];
      rw [proof_in_Class]; simp only [ordered_pair_eq_iff, ↓existsAndEq,
        and_true, exists_eq_left']; exact ⟨h61, h62⟩;
    have hx2 := value_func hg1.2 hx1; rw [hx2, h6t]; exact ⟨h61, h62⟩;
  have h7t : A = has_belong.to_Class A := rfl; conv at hx => ext; lhs; rw [h7t];
  have h71 := rec_choose1 (fun α ↦ restrict_is_set f1.1) (fun α ↦ (hx α).1);
  have h72 := rec_choose2 (fun α ↦ restrict_is_set f1.1) (fun α ↦ (hx α).1);
  constructor; constructor;
  · exact ⟨⟨f1.1.1, h72⟩, f1.2⟩;
  · have h8 : _;
    · apply th7_45 h2 h71; intro x hx1 y hy1 hy2;
      rw [has_function.proof_range] at hy1; rcases hy1 with ⟨α, hy1⟩;
      have hy3 := value_func f1.1.2 hy1;
      have hα := (has_function.proof_domain _).2 ⟨_, hy1⟩; rw [←f1.2] at hα;
      let α : ordinal := ⟨α, hα⟩; have hy5 := (hx α).2;
      rw [←f2, hy3, well_found_eqv_class] at hy5; have hy5 := hy5 x;
      rw [Iff.intro Function.swap Function.swap] at hy5;
      have hy5 := hy5 hy2; rw [class_sub_is_sub] at hy5;
      simp only [imp_false, not_and, not_not, has_function.proof_range,
        pair_in_restrict] at hy5; rw [has_function.proof_range];
      rcases hy5 hx1 with ⟨z, hy5⟩; exact ⟨z, hy5.1⟩;
    cases h8 with
    | inl => symm; assumption;
    | inr h8 =>
      exfalso; rcases h8 with ⟨x, hx1, hx2⟩;
      have hx3 := h2.1.2 x hx1; rw [←hx2, ←domain_inv] at hx3;
      have hx3 := @class_is_set_range _ (domain_is_set ⟨inverse_is_relation, h72.2⟩ hx3);
      rw [range_inv, ←f1.2] at hx3; exact On_proper_class hx3;
  intro x' hx2 y' hy; let x : ordinal := ⟨x', hx2⟩; let y : ordinal := ⟨y', hy⟩;
  simp only [E_simp]; suffices ht : ∀ x y : ordinal, x < y →
    R& ((trans_rec_class G)[[x.val]]) ((trans_rec_class G)[[y.val]]);
  · constructor; · exact ht x y;
    have ht := ht y x; intro ht1; cases @ord_total x y with
    | inl => assumption;
    | inr ht2 => cases ht2 with
      | inl ht2 =>
        have ht2 : x' = y'; · exact Subtype.coe_inj.2 ht2;
        subst y'; exfalso;
        refine foundational_belong_to_self h2.1.1 _ ?_ ht1;
        · rw [f2 x]; exact (hx _).1.1;
      | inr ht2 =>
        have ht := ht ht2; simp only at ht; exfalso;
        refine foundational_belong_to_2 h2.1.1 _ ?_ _ ?_ ht1 ht;
        · rw [f2 x]; exact (hx _).1.1;
        rw [f2 y]; exact (hx _).1.1;
  intro x y h;
  have hy1 : A - (trans_rec_class G)[y.val] s⊆ A - (trans_rec_class G)[x.val];
  · intro a; simp only [class_sub_is_sub, has_function.proof_range, pair_in_restrict,
    not_exists, not_and, and_imp];
    intro ha1 ha2; use ha1; intro z hz hx3; apply ha2 z hz;
    exact y.prop.1 x.val h z hx3;
  rw [←h7t] at hx; have hy2 := hy1 _ (hx _).1; have hy3 := (hx x).2;
  rw [well_found_eqv_class] at hy3; have hy3 := hy3 _ hy2;
  have hy4 := (hx x).1; simp only [←f2] at hy3 hy2 hy4;
  cases h2.2.2 _ hy4.1 _ hy2.1 with
  | inl => assumption;
  | inr hy5 => cases hy5 with
    | inl hy5 =>
      have hox : x ∈ On := x.prop; have hoy : y ∈ On := y.prop;
      rw [f1.2] at hox hoy;
      have hyx := value_func2 f1.1.2 hox; have hyy := value_func2 f1.1.2 hoy;
      rw [hy5] at hyx; rw [←pair_in_inverse] at hyx hyy;
      have hye := Subtype.ext (h72.2 _ _ _ ⟨hyx, hyy⟩); subst y;
      exfalso; exact belong_to_self h;
    | inr hy5 => exfalso; exact hy3 hy5;
theorem ord_isom_ord_class {A G : Class} (h1 : ¬A.is_set) (h2 : A s⊆ On)
  (hg : G = fun c ↦ ∃ x y, c = s⟨x, y⟩ ∧ y ∈ A - W(x) ∧
    (A - W(x)) ∩ E⁻¹[s{y}] = s0) : Isom (trans_rec_class G) E E On A := by
  refine ord_isom_wfwo_class h1 ?_ hg; use E_well_founded; exact E_well_order_ord_class h2;

theorem ord_isom_we_set [has_belong α] [has_intersection α Class] [has_value α]
  [has_intersection set α] [has_intersection Class α] {a : set} {R : α}
  (h : is_well_order R a) :
  ∃! α : ordinal, ∃ f : set, Isom f E R α.val a := by
  let G : Class := fun c ↦ ∃ x y, c = s⟨x, y⟩ ∧ y ∈ a.to_Class - W(x) ∧
    (a.to_Class - W(x)) ∩ R⁻¹[s{y}] = s0;
  have f1 := @transfinite_recursion1 G;
  have f2 := fun α ↦ @transfinite_recursion2 G α (restrict_is_set f1.1);
  have h2 := @rec_choose_set a G (fun α ↦ restrict_is_set f1.1);
  have t1 := @th7_482 a.to_Class R G ⟨⟨h.1, well_founded_on_set⟩, h⟩;
  have h3 : _;
  · apply h2; intro α ha;

end zfset
