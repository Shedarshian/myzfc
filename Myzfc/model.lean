import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal
import Myzfc.ac

namespace zfset
open Lean

-- inductive wff where
-- | error
-- | token (s : Name)
-- | mem (x1 x2 : wff)
-- | and (x1 x2 : wff)
-- | or (x1 x2 : wff)
-- | imp (x1 x2 : wff)
-- | iff (x1 x2 : wff)
-- | neg (x1 : wff)
-- | foral (x1 : Name) (x2 : wff)
-- | exist (x1 : Name) (x2 : wff)
-- | notmem (x1 x2 : wff)
-- | eq (x1 x2 : wff)
-- | subseteq (x1 x2 : wff)
-- | make_pair (x1 x2 : wff)
-- | make_union (x1 : wff)
-- deriving Nonempty

-- syntax:max "wff{" term "}" : term
-- macro_rules
-- | `(wff{$t:term}) =>
--   match t with
--   | `($y:ident) => `(wff.token $(quote y.getId))
--   | `($x1:term ∈ $x2:term) => `(wff.mem (wff{$x1}) (wff{$x2}))
--   | `($x1:term ∧ $x2:term) => `(wff.and (wff{$x1}) (wff{$x2}))
--   | `($x1:term ∨ $x2:term) => `(wff.or (wff{$x1}) (wff{$x2}))
--   | `($x1:term → $x2:term) => `(wff.imp (wff{$x1}) (wff{$x2}))
--   | `($x1:term ↔ $x2:term) => `(wff.iff (wff{$x1}) (wff{$x2}))
--   | `(¬ $x1:term) => `(wff.neg (wff{$x1}))
--   | `(($x1:term)) => `(wff{$x1})
--   | `(∀ $x1:ident : set, $x2:term) => `(wff.foral $(quote x1.getId) (wff{$x2}))
--   | `(∀ $x1:ident* : set, $x2:term) => do
--       let init ← `(wff{$x2})
--       x1.foldlM (fun x acc ↦ `(wff.foral $(quote x.getId) ($acc))) init
--   | `(∃ $x1:ident : set, $x2:term) => `(wff.exist $(quote x1.getId) (wff{$x2}))
--   | `($x1:term ∉ $x2:term) => `(wff.notmem (wff{$x1}) (wff{$x2}))
--   | `($x1:term = $x2:term) => `(wff.eq (wff{$x1}) (wff{$x2}))
--   | `($x1:term s⊆ $x2:term) => `(wff.subseteq (wff{$x1}) (wff{$x2}))
--   | `(s{$x1:term, $x2:term}) => `(wff.make_pair (wff{$x1}) (wff{$x2}))
--   | `(∪($x1:term)) => `(wff.make_union (wff{$x1}))
--   | _ => `(wff.error)

-- def from_wff (a : wff) : MacroM (TSyntax `term) :=
--   match a with
--   | wff.token s => do let stx := mkIdent s; `($stx)
--   | wff.mem x1 x2 => do `($(← from_wff x1):term ∈ $(← from_wff x2):term)
--   | wff.and x1 x2 => do `($(← from_wff x1):term ∧ $(← from_wff x2):term)
--   | wff.or x1 x2 => do `($(← from_wff x1):term ∨ $(← from_wff x2):term)
--   | wff.imp x1 x2 => do `($(← from_wff x1):term → $(← from_wff x2):term)
--   | wff.iff x1 x2 => do `($(← from_wff x1):term ↔ $(← from_wff x2):term)
--   | wff.neg x1 => do `(¬ $(← from_wff x1):term)
--   | wff.foral x1 x2 => do let stx := mkIdent x1; `(∀ $stx : set, $(← from_wff x2):term)
--   | wff.exist x1 x2 => do let stx := mkIdent x1; `(∃ $stx:ident : set, $(← from_wff x2):term)
--   | wff.notmem x1 x2 => do `($(← from_wff x1):term ∉ $(← from_wff x2):term)
--   | wff.eq x1 x2 => do `($(← from_wff x1):term = $(← from_wff x2):term)
--   | wff.subseteq x1 x2 => do `($(← from_wff x1):term s⊆ $(← from_wff x2):term)
--   | wff.make_pair x1 x2 => do `(s{$(← from_wff x1):term, $(← from_wff x2):term})
--   | wff.make_union x1 => do `(∪($(← from_wff x1):term))
--   | wff.error => Macro.throwError "cannot convert wff.error to syntax"
-- def wff_to_scope (A : Class) (a : wff) : MacroM (TSyntax `term) :=
--   match a with
--   | wff.token s => `($s:ident ∩ A)
--   | wff.mem x1 x2 => do `($(← wff_to_scope A x1):term ∈ $(← wff_to_scope A x2):term)
--   | wff.and x1 x2 => do `($(← wff_to_scope A x1):term ∧ $(← wff_to_scope A x2):term)
--   | wff.or x1 x2 => do `($(← wff_to_scope A x1):term ∨ $(← wff_to_scope A x2):term)
--   | wff.imp x1 x2 => do `($(← wff_to_scope A x1):term → $(← wff_to_scope A x2):term)
--   | wff.iff x1 x2 => do `($(← wff_to_scope A x1):term ↔ $(← wff_to_scope A x2):term)
--   | wff.neg x1 => do `(¬ $(← wff_to_scope A x1):term)
--   | wff.foral x1 x2 => do `(∀ $x1:ident : set, $x1 ∈ A → $(← wff_to_scope A x2):term)
--   | wff.exist x1 x2 => do `(∃ $x1:ident : set, $x1 ∈ A ∧ $(← wff_to_scope A x2):term)
--   | wff.notmem x1 x2 => do `($(← wff_to_scope A x1):term ∉ $(← wff_to_scope A x2):term)
--   | wff.eq x1 x2 => do `($(← wff_to_scope A x1):term = $(← wff_to_scope A x2):term)
--   | wff.subseteq x1 x2 => do `($(← wff_to_scope A x1):term s⊆ $(← wff_to_scope A x2):term)
--   | wff.make_pair x1 x2 => do `(s{$(← wff_to_scope A x1):term, $(← wff_to_scope A x2):term} ∩ A)
--   | wff.make_union x1 => do `(∪($(← wff_to_scope A x1):term) ∩ A)
--   | wff.error => Macro.throwError "cannot convert wff.error to syntax"
-- syntax:max "from_wff{" term "}" : term
-- macro_rules
-- | `(from_wff{$t:term}) =>


-- def Ax1 := wff{∀ a : set, x = y → x ∈ a → y ∈ a}

private def mkAllMem (A : TSyntax `ident) (xs : Array (TSyntax `ident)) :
    MacroM (TSyntax `term) := do
  match xs.back? with
  | none =>
      `(True)
  | some last =>
      xs.pop.foldrM
        (init := ← `($last ∈ $A))
        fun x rest =>
          `($x ∈ $A ∧ $rest)

syntax:100 "|" ident "(" ident,* ")m{" term "}" : term
macro_rules
| `(|$A:ident($xs:ident,*)m{$t:term}) =>
  match t with
  | `($y:ident) =>
      if xs.getElems.any (·.getId.eraseMacroScopes == y.getId.eraseMacroScopes)
          then `($y ∩ $A) else
          Lean.Macro.throwError s!"identifier '{y.getId}' is not present in the list"
  | `($x1:term ∈ $x2:term) => `(|$A($xs,*)m{$x1} ∈ |$A($xs,*)m{$x2})
  | `($x1:term ∧ $x2:term) => `(|$A($xs,*)m{$x1} ∧ |$A($xs,*)m{$x2})
  | `($x1:term ∨ $x2:term) => `(|$A($xs,*)m{$x1} ∨ |$A($xs,*)m{$x2})
  | `($x1:term → $x2:term) => `(|$A($xs,*)m{$x1} → |$A($xs,*)m{$x2})
  | `($x1:term ↔ $x2:term) => `(|$A($xs,*)m{$x1} ↔ |$A($xs,*)m{$x2})
  | `(¬$x1:term) => `(¬|$A($xs,*)m{$x1})
  | `(($x1:term)) => `((|$A($xs,*)m{$x1}))
  | `(∀ $x1:ident : set, $x2:term) => `(∀ $x1:ident : set, $x1 ∈ $A → |$A($x1,$xs,*)m{$x2})
  | `(∀ $x1:ident* : set, $x2:term) => do
      let h ← mkAllMem A x1;
      let allXs := x1 ++ xs.getElems;
      `(∀ $x1* : set, $h → |$A($allXs,*)m{$x2})
  | `(∃ $x1:ident : set, $x2:term) => `(∃ $x1:ident : set, $x1 ∈ $A ∧ |$A($x1,$xs,*)m{$x2})
  | `($x1:term ∉ $x2:term) => `(|$A($xs,*)m{¬$x1 ∈ $x2})
  | `($x1:term = s0) => `(|$A($xs,*)m{∀ _x : set, _x ∉ $x1})
  | `($x1:term = $x2:term) => `(|$A($xs,*)m{∀ _x : set, _x ∈ $x1 ↔ _x ∈ $x2})
  | `($x1:term ≠ $x2:term) => `(|$A($xs,*)m{¬$x1 = $x2})
  | `($x1:term s⊆ $x2:term) => `(|$A($xs,*)m{∀ _x : set, _x ∈ $x1 → _x ∈ $x2})
  | `(s{$x1:term, $x2:term}) => `(s{|$A($xs,*)m{$x1}, |$A($xs,*)m{$x2}} ∩ $A)
  | `(∪($x1:term)) => `(∪(|$A($xs,*)m{$x1}) ∩ $A)
  | `($x1:term ∩ $x2:term) => `(|$A($xs,*)m{$x1} ∩ |$A($xs,*)m{$x2} ∩ $A)
  | _ => Lean.Macro.throwError s!"syntax '{t}' is not defined"
syntax:max "|" ident "(" ident,* ")abs{" term "}" : term
macro_rules
| `(|$A:ident($xs:ident,*)abs{$t:term}) => do
  let h ← mkAllMem A xs.getElems; `($h → (|$A($xs,*)m{$t} ↔ $t))

syntax:max "|" ident "()ax{Ax1}" : term
macro_rules |`(|$A:ident()ax{Ax1}) => `(|$A()abs{∀ a x y : set, x = y → x ∈ a → y ∈ a})
syntax:max "|" ident "()ax{Ax2}" : term
macro_rules |`(|$A:ident()ax{Ax2}) => `(|$A()abs{∀ a b : set, ∃ x : set, x = s{a, b}})
syntax:max "|" ident "()ax{Ax3}" : term
macro_rules |`(|$A:ident()ax{Ax3}) => `(|$A()abs{∀ a : set, ∃ x : set, x = ∪(a)})
syntax:max "|" ident "()ax{Ax4}" : term
macro_rules |`(|$A:ident()ax{Ax4}) => `(|$A()abs{∀ a : set, ∃ x : set, ∀ y : set, (y ∈ x ↔ y s⊆ a)})
syntax:max "|" ident "()ax{Ax6}" : term
macro_rules |`(|$A:ident()ax{Ax6}) => `(|$A()abs{∀ a : set, a ≠ s0 → ∃ x : set, x ∈ a ∧ x ∩ a = s0})

theorem abs_ident {A : Class} {x : set} : Tr(A) → x ∈ A → |A(x)m{x} = x :=
  fun h1 h2 ↦ Eq.symm (subseteq_iff_eq_intersection.1 (h1 x h2))
theorem abs_in {A : Class} {x y : set} : Tr(A) → |A(x,y)abs{x ∈ y} :=
  by intro h1 ⟨h2, _⟩; simp only [abs_ident h1 h2, intersection_def, h2, and_true]
theorem abs_subset {A : Class} {x y : set} : Tr(A) → |A(x,y)abs{x s⊆ y} := by
  intro h1 ⟨h2, h3⟩; simp only [abs_ident h1 h2, abs_ident h1 h3];
  constructor <;> intro h z hz;
  · have hz1 := h1 _ h2 _ hz; have hz2 := h _ hz1; have hz3 := abs_ident h1 hz1;
    simp only [hz3] at hz2; exact hz2 hz;
  simp only [abs_ident h1 hz]; exact h _;
theorem abs_eq {A : Class} {x y : set} : Tr(A) → |A(x,y)abs{x = y} := by
  intro h1 ⟨h2, h3⟩; rw [←extensionality_belong]; simp only [abs_ident h1 h2, abs_ident h1 h3];
  constructor <;> intro h z;
  · constructor;  all_goals
      intro hz; have hz1 := h1 _ ?_ _ hz; assumption'; have hz2 := h _ hz1;
      have hz3 := abs_ident h1 hz1; simp only [hz3] at hz2; first | rwa [hz2] | rwa [←hz2];
  intro hz; simp only [abs_ident h1 hz]; exact h _;
theorem abs_pair2 {A : Class} {x y : set} : Tr(A) → x ∈ A → y ∈ A → s{x, y} ∩ A = s{x, y} := by
  intro h h1 h2; rw [←extensionality_belong]; intro a;
  simp only [intersection_def, axiom_of_pair, and_iff_left_iff_imp];
  intro ha; cases' ha <;> subst a <;> assumption;
theorem abs_pair {A : Class} {x y : set} : Tr(A) → x ∈ A → y ∈ A → |A(x,y)m{s{x, y}} = s{x, y} := by
  intro h h1 h2; rw [←extensionality_belong]; intro a; rw [←abs_pair2 h h1 h2];
  simp only [abs_ident h h1, abs_ident h h2, intersection_def, axiom_of_pair];
theorem abs_union2 {A : Class} {x : set} : Tr(A) → x ∈ A → ∪(x) ∩ A = ∪(x) := by
  intro h1 h2; rw [←extensionality_belong]; intro a; simp only [intersection_def,
    and_iff_left_iff_imp]; intro h3;
  rw [make_union_reloaded, has_union.proof_union] at h3; rcases h3 with ⟨c, h3, h4⟩;
  exact h1 _ (h1 _ h2 _ h4) _ h3;
theorem abs_union {A : Class} {x : set} : Tr(A) → x ∈ A → |A(x)m{∪(x)} = ∪(x) := by
  intro h1 h2; rw [←abs_union2 h1 h2, abs_ident h1 h2];

theorem abs_axiom1 {A : Class} : Tr(A) → |A()ax{Ax1} :=
by
  intro h2 _; simp only [intersection_def, and_congr_left_iff, and_imp, forall_eq', imp_self,
    implies_true, iff_true];
  intro a x y ha hx hy h3 h4 h5; have h6 := abs_eq h2 ⟨hx, hy⟩;
  simp only [abs_ident h2 hx, abs_ident h2 hy] at *;
  have h7 : ∀ z : set, z ∈ A → z ∩ A ∈ A; · intro z hz; rwa [abs_ident h2 hz];
  have h3 := fun z hz ↦ h3 z hz (h7 z hz); rw [h6] at h3; subst y; use h4;
theorem abs_axiom2 {A : Class} : Tr(A) → (|A()ax{Ax2} ↔ ∀ a s∈ A, ∀ b s∈ A, s{a, b} ∈ A) := by
  intro h2; simp only [and_imp, forall_const, ↓existsAndEq, implies_true, iff_true];
  constructor <;> intro h a1 a2 a3 a4 <;> have h := h a1 a3 a2 a4;
  · rcases h with ⟨x, x1, x2⟩; rw [abs_pair h2 a2 a4] at x2;
    suffices x3 : x = s{a1, a3}; · subst x; assumption;
    rw [←extensionality_belong]; simp only [axiom_of_pair]; intro a; constructor <;> intro b1;
    all_goals
      first | have x3 := h2 _ x1 _ b1;
            | have x3 : a ∈ A; · cases' b1 <;> subst a <;> assumption;
      have x4 := x2 a x3;
      rw [abs_ident h2 x3, abs_ident h2 x1, axiom_of_pair] at x4;
      first | rwa [←x4]; | rwa [x4];
  use s{a1, a2}; use h; intro x x1; simp only [abs_pair h2 a3 a4, abs_pair2 h2 a3 a4];
theorem abs_axiom3 {A : Class} : Tr(A) → (|A()ax{Ax3} ↔ ∀ a s∈ A, ∪(a) ∈ A) := by
  intro h2; simp only [intersection_def, and_congr_left_iff, ↓existsAndEq, implies_true, iff_true,
    forall_const];
  constructor <;> intro h a a1 <;> have h := h a a1 <;> rw [abs_ident h2 a1] at *;
  · rcases h with ⟨x, x1, x2⟩; suffices x3 : x = ∪(a); · subst x; assumption;
    have h7 : ∀ z : set, z ∈ A → z ∩ A ∈ A; · intro z hz; rwa [abs_ident h2 hz];
    have x2 := fun z hz ↦ x2 z hz (h7 z hz);
    rw [←extensionality_belong]; intro z; constructor <;> intro b1;
    all_goals
      first | have x3 := h2 _ x1 _ b1;
            | have b1' := b1; rw [make_union_reloaded, has_union.proof_union] at b1;
              rcases b1 with ⟨c, b1, b2⟩; have x3 := h2 _ (h2 _ a1 _ b2) _ b1;
      have x2 := x2 _ x3; rw [abs_ident h2 x3] at x2;
      first | rwa [←x2]; | rwa [x2];
  use ∪(a); use h; intro x x1 x2; rw [abs_ident h2 x1];
theorem abs_axiom4 {A : Class} : Tr(A) → (|A()ax{Ax4} ↔ ∀ a s∈ A, P(a) ∩ A ∈ A) := by
  intro h2; suffices h : |A()ax{Ax4} ↔ (∀ a s∈ A, ∃ x s∈ A, ∀ y s∈ A, (y ∈ x ↔ y s⊆ a));
  · rw [h]; constructor <;> intro h a a1 <;> have h := h a a1;
    · rcases h with ⟨x, h, x1⟩; suffices x2 : x = P(a) ∩ A; · subst x2; assumption;
      rw [←extensionality_belong]; intro y; simp only [intersection_def]; constructor <;> intro y1;
      all_goals
        first | have x3 := y1.2; | have x3 := h2 _ h _ y1;;
        have x1 := x1 _ x3; simp only [axiom_of_power] at *;
        first | rw [x1]; exact y1.1; | rw [←x1]; use y1;
    use P(a) ∩ A; use h; intro x x1;
    simp only [intersection_def, axiom_of_power, and_iff_left_iff_imp];
    intro x2; assumption;
  have ha4 : ∀ (a : set), ∃ x : set, ∀ (y : set), y ∈ x ↔ y s⊆ a;
  · intro a; use P(a); simp only [axiom_of_power, implies_true];
  simp only [forall_const, ha4]; simp only [implies_true, iff_true];
  constructor;
    all_goals
      intro h a a1; have h := h a a1; rcases h with ⟨x, x1, x2⟩; use x; use x1;
      intro y y1; have x2 := x2 _ y1;
      simp only [abs_ident h2 x1, abs_ident h2 y1, abs_ident h2 a1] at *; rw [x2, subseteq];
      constructor <;> intro z1 z z2 <;> have z1 := z1 z <;>
      first | have z3 : z ∈ A := h2 _ y1 _ z2; | have z3 : z ∈ A := z2;
      all_goals rw [abs_ident h2 z3] at *;; assumption'; exact z1 z3 z2;
theorem abs_axiom6 {A : Class} : Tr(A) → |A()ax{Ax6} := by
  intro h2; simp only [intersection_def, not_and, not_forall, not_not,
    intersection_assoc, forall_exists_index, ne_eq, forall_const];
  have h : ∀ (a : set), ¬a = s0 → ∃ x, x ∈ a ∧ x ∩ a = s0; · intro a; exact axiom_of_regularity;
  constructor <;> intro z; · assumption;
  intro a a1 x x1 x2 x3; simp only [abs_ident h2 x1] at x2;
  have x4 := nonempty_iff_has_element.2 ⟨_, x2⟩;
  have x5 := h _ x4; rcases x5 with ⟨z, x5, x6⟩;
  use z; have z1 := h2 _ a1 _ x5; simp only [abs_ident h2 z1]; use z1; use ⟨x5, z1⟩;
  intro y y1 y2 y3 y4 y5 y6; simp only [abs_ident h2 y1] at *;
  rw [←extensionality_belong] at x6; simp only [intersection_comm, intersection_def, empty_false,
    iff_false, not_and] at x6; exact x6 _ y4 y2;

end zfset
