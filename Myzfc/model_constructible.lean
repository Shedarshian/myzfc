import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal
import Myzfc.ac
import Myzfc.model

namespace zfset

noncomputable def cnv2 (a : set) := {s⟨z, x, y⟩ // s⟨x, y, z⟩ p∈ a}
noncomputable def cnv3 (a : set) := {s⟨x, z, y⟩ // s⟨x, y, z⟩ p∈ a}

noncomputable def funo1 (a b : set) := s{a, b}
noncomputable def funo2 (a _ : set) := a ∩ E
noncomputable def funo3 (a b : set) := a - b
noncomputable def funo4 (a b : set) := a Γ b
noncomputable def funo5 (a b : set) := a ∩ D(b)
noncomputable def funo6 (a b : set) := a ∩ b⁻¹
noncomputable def funo7 (a b : set) := a ∩ cnv2 b
noncomputable def funo8 (a b : set) := a ∩ cnv3 b

def close (A : Class) (f : set → set → set) := ∀ a s∈ A, ∀ b s∈ A, f a b ∈ A
def close_funo (A : Class) := close A funo1 ∧ close A funo2 ∧ close A funo3 ∧ close A funo4 ∧
  close A funo5 ∧ close A funo6 ∧ close A funo7 ∧ close A funo8

theorem stm_close_funo1 : Tr(A) → abs_ax2 A → close A funo1 := by
  intro h h2 a ha b hb;
  rw [abs_axiom2 h] at h2; exact h2 a ha b hb;
theorem stm_close_funo2 : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close A funo2 := by
  intro h h2 h5 a ha b hb;
  have h5 := fun φ ↦ @abs_axiom5_separation φ A h h5 a ha;
  convert_to {x s∈ a // ∃ c d, x = s⟨c, d⟩ ∧ c ∈ d} ∈ A;
  · rw [←extensionality_belong]; intro x; simp only [funo2, intersection_def, set_separation,
    and_congr_right_iff];
    intro hx; unfold E; simp [proof_in_Class, and_comm];
  have s : ∀ x, A|abs{∃ c, ∃ d, x = s⟨c, d⟩ ∧ c ∈ d};
  · intro x hx; apply abs_exists <;> intro c hc;
    · apply abs_exists <;> intro d hd;
      · exact abs_and (abs_eq_opair h h2 ⟨hx, hc, hd⟩) (abs_memset h ⟨hc, hd⟩);
      simp only [wff_and, wff_eq_term, wff_term, tm_opair, ← set_eq_iff_class, wff_mem] at hd;
      have d2 : d ∈ s{c, d} ∧ s{c, d} ∈ x; · rw [hd.1]; simp [make_ordered_pair];
      exact h _ (h _ hx _ d2.2) _ d2.1;
    simp only [wff_neg, wff_foral, wff_and, wff_eq_term, wff_term, tm_opair, ← set_eq_iff_class,
      wff_mem, not_and, not_forall, not_not] at hc; rcases hc with ⟨d, d1, d2⟩; subst x;
    have d1 : c ∈ s{c} ∧ s{c} ∈ s⟨c, d⟩; · simp [make_ordered_pair];
    exact h _ (h _ hx _ d1.2) _ d1.1;
  convert_to {x s∈ a // A⊨{∃ c, ∃ d, x = s⟨c, d⟩ ∧ c ∈ d}} ∈ A;
  · rw [separation_eq]; intro x hx1; have hx := h _ ha _ hx1;
    rw [uf (s x hx)]; simp [←set_eq_iff_class];
  apply h5;
theorem stm_close_funo3 : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close A funo3 := by
  intro h h2 h5 a ha b hb;
  have h5 := fun φ ↦ @abs_axiom5_separation φ A h h5 a ha;
  convert_to {x s∈ a // ¬x ∈ b} ∈ A;
  · rw [←extensionality_belong]; intro x; simp only [funo3, set_sub_is_sub, set_separation,
    intersection_def, and_congr_right_iff]; intro hx; rfl;
  have s : ∀ x, A|abs{¬x ∈ b};
  · intro x hx; apply abs_neg; exact abs_memset h hx;
  convert_to {x s∈ a // A⊨{¬x ∈ b}} ∈ A;
  · rw [separation_eq]; intro x hx1; have hx := h _ ha _ hx1;
    rw [uf (s x ⟨hx, hb⟩)]; simp only [wff_neg, wff_mem];
  apply h5;
theorem stm_close_funo4 : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close A funo4 := by
  intro h h2 h5 a ha b hb;
  have h5 := fun φ ↦ @abs_axiom5_separation φ A h h5 a ha;
  convert_to {x s∈ a // ∃ c d, x = s⟨c, d⟩ ∧ c ∈ b} ∈ A;
  · rw [←extensionality_belong]; intro x; simp only [funo4, intersection_def, set_separation,
    and_congr_right_iff, belong_restrict];
    intro hx; simp only [and_comm, exists_and_left, proof_in_Class];
  have s : ∀ x, A|abs{∃ c, ∃ d, x = s⟨c, d⟩ ∧ c ∈ b};
  · intro x ⟨hx, hb⟩; apply abs_exists <;> intro c hc;
    · apply abs_exists <;> intro d hd;
      · exact abs_and (abs_eq_opair h h2 ⟨hx, hc, hd⟩) (abs_memset h ⟨hc, hb⟩);
      simp only [wff_and, wff_eq_term, wff_term, tm_opair, ← set_eq_iff_class, wff_mem] at hd;
      have d2 : d ∈ s{c, d} ∧ s{c, d} ∈ x; · rw [hd.1]; simp [make_ordered_pair];
      exact h _ (h _ hx _ d2.2) _ d2.1;
    simp only [wff_neg, wff_foral, wff_and, wff_eq_term, wff_term, tm_opair, ← set_eq_iff_class,
      wff_mem, not_and, not_forall, not_not] at hc; rcases hc with ⟨d, d1, d2⟩; subst x;
    have d1 : c ∈ s{c} ∧ s{c} ∈ s⟨c, d⟩; · simp [make_ordered_pair];
    exact h _ (h _ hx _ d1.2) _ d1.1;
  convert_to {x s∈ a // A⊨{∃ c, ∃ d, x = s⟨c, d⟩ ∧ c ∈ b}} ∈ A;
  · rw [separation_eq]; intro x hx1; have hx := h _ ha _ hx1;
    rw [uf (s x ⟨hx, hb⟩)]; simp [←set_eq_iff_class];
  apply h5;
theorem stm_close_funo5 : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close A funo5 := by
  intro h h2 h5 a ha b hb;
  have h5 := fun φ ↦ @abs_axiom5_separation φ A h h5 a ha;
  convert_to {x s∈ a // ∃ y, s⟨x, y⟩ ∈ b} ∈ A;
  · rw [←extensionality_belong]; intro x; simp only [funo5, intersection_def,
    has_function.proof_domain, set_separation, and_congr_right_iff];
    intro hx; simp [proof_in_Class];
  have s : ∀ x, A|abs{∃ y, s⟨x, y⟩ ∈ b};
  · intro x ⟨hx, hb⟩; apply abs_exists <;> intro c hc;
    · apply abs_exists <;> intro d hd;
      · exact abs_and (abs_eq_opair h h2 ⟨hd, hx, hc⟩) (abs_memset h ⟨hd, hb⟩);
      simp only [term.ofSet, wff_and, wff_eq_term, wff_term, tm_opair, ← set_eq_iff_class,
        wff_mem] at hd;
      exact h _ hb _ hd.2;
    simp only [term.mem, term.ofSet, wff_neg, wff_foral, wff_and, wff_eq_term, wff_term, tm_opair,
      ← set_eq_iff_class, wff_mem, not_and, forall_eq, not_not] at hc;
    have d1 : c ∈ s{x, c} ∧ s{x, c} ∈ s⟨x, c⟩; · simp [make_ordered_pair];
    exact h _ (h _ (h _ hb _ hc) _ d1.2) _ d1.1;
  convert_to {x s∈ a // A⊨{∃ y, s⟨x, y⟩ ∈ b}} ∈ A;
  · rw [separation_eq]; intro x hx1; have hx := h _ ha _ hx1;
    rw [uf (s x ⟨hx, hb⟩)]; simp [term.mem, ←set_eq_iff_class];
  apply h5;
theorem stm_close_funo6 : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close A funo6 := by
  intro h h2 h5 a ha b hb;
  have h5 := fun φ ↦ @abs_axiom5_separation φ A h h5 a ha;
  convert_to {x s∈ a // ∃ c d, x = s⟨c, d⟩ ∧ s⟨d, c⟩ ∈ b} ∈ A;
  · rw [←extensionality_belong]; intro x; simp only [funo6, intersection_def, set_separation,
    and_congr_right_iff];
    intro hx; simp only [has_function.proof_inverse, proof_in_Class];
    rw [exists_comm]; simp [and_comm];
  have s : ∀ x, A|abs{∃ c, ∃ d, x = s⟨c, d⟩ ∧ s⟨d, c⟩ ∈ b};
  · intro x ⟨hx, hb⟩; apply abs_exists <;> intro c hc;
    · apply abs_exists <;> intro d hd;
      · apply abs_and (abs_eq_opair h h2 ⟨hx, hc, hd⟩); apply abs_exists <;> intro e he;
        · exact abs_and (abs_eq_opair h h2 ⟨he, hd, hc⟩) (abs_memset h ⟨he, hb⟩);
        simp only [term.ofSet, wff_and, wff_eq_term, wff_term, tm_opair, ← set_eq_iff_class,
          wff_mem] at he; exact h _ hb _ he.2;
      simp only [term.mem, term.ofSet, wff_and, wff_eq_term, wff_term, tm_opair, ← set_eq_iff_class,
        wff_neg, wff_foral, wff_mem, not_and, forall_eq, not_not] at hd;
      have d2 : d ∈ s{c, d} ∧ s{c, d} ∈ x; · rw [hd.1]; simp [make_ordered_pair];
      exact h _ (h _ hx _ d2.2) _ d2.1;
    simp only [term.mem, term.ofSet, wff_neg, wff_foral, wff_and, wff_eq_term, wff_term, tm_opair,
      ← set_eq_iff_class, wff_mem, not_and, forall_eq, not_not, not_forall] at hc;
      rcases hc with ⟨d, d1, d2⟩; subst x;
    have d1 : c ∈ s{c} ∧ s{c} ∈ s⟨c, d⟩; · simp [make_ordered_pair];
    exact h _ (h _ hx _ d1.2) _ d1.1;
  convert_to {x s∈ a // A⊨{∃ c, ∃ d, x = s⟨c, d⟩ ∧ s⟨d, c⟩ ∈ b}} ∈ A;
  · rw [separation_eq]; intro x hx1; have hx := h _ ha _ hx1;
    rw [uf (s x ⟨hx, hb⟩)]; simp [←set_eq_iff_class, term.mem];
  apply h5;
theorem stm_close_funo7 : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close A funo7 := by sorry
theorem stm_close_funo8 : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close A funo8 := by sorry
theorem stm_close_funo : Tr(A) → abs_ax2 A → (∀ φ, abs_ax5 A φ) → close_funo A :=
  fun a b c ↦ ⟨stm_close_funo1 a b, stm_close_funo2 a b c, stm_close_funo3 a b c,
  stm_close_funo4 a b c, stm_close_funo5 a b c, stm_close_funo6 a b c, stm_close_funo7 a b c,
  stm_close_funo8 a b c⟩



end zfset
