import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal
import Myzfc.ac

namespace zfset
open Lean

inductive wff where
| True
| False
| mem (x1 x2 : set)
| imp (x1 x2 : wff)
| neg (x1 : wff)
| foral (body : set → wff)
abbrev term := set → wff

syntax:max "wff{" term "}" : term
macro_rules | `(wff{$t:ident}) => `($t)
macro_rules | `(wff{($x1:term)}) => `((wff{$x1}))
syntax:max "tm{" term "}" : term
macro_rules | `(tm{($x1:term)}) => `((tm{$x1}))
macro_rules | `(tm{|$t|}) => `($t)

macro_rules | `(wff{$x1:term → $x2:term}) => `(wff.imp (wff{$x1}) (wff{$x2}))
macro_rules | `(wff{¬$x1:term}) => `(wff.neg (wff{$x1}))
def wff.and (x1 x2 : wff) := wff{¬(x1 → ¬x2)}
macro_rules | `(wff{$x1:term ∧ $x2:term}) => `(wff.and wff{$x1} wff{$x2})
def wff.or (x1 x2 : wff) := wff{¬x1 → x2}
macro_rules | `(wff{$x1:term ∨ $x2:term}) => `(wff.or wff{$x1} wff{$x2})
def wff.iff (x1 x2 : wff) := wff{(x1 → x2) ∧ (x2 → x1)}
macro_rules | `(wff{$x1:term ↔ $x2:term}) => `(wff.iff wff{$x1} wff{$x2})
macro_rules | `(wff{∀ $x1:ident, $x2:term}) => `(wff.foral (fun $x1 ↦ wff{$x2}))
macro_rules | `(wff{∀ $x1:ident*, $x2:term}) => do
      let init ← `(wff{$x2})
      let r ← x1.foldrM (fun x (acc : TSyntax `term) ↦ `(wff.foral (fun $x ↦ ($acc)))) init
      return r.raw
macro_rules | `(wff{∃ $x1:ident, $x2:term}) => `(wff{¬∀ $x1, ¬$x2})
macro_rules | `(wff{|$x|}) => `($x)
macro_rules | `(wff{true}) => `(wff.True)
macro_rules | `(wff{false}) => `(wff.False)

@[simp] def term.ofSet (a : set) : term := fun x ↦ wff.mem x a
@[simp] def term.memSet (x : set) (t : term) : wff := t x
def term.eq (a b : term) : wff := wff{∀ x, |a x| ↔ |b x|}
def term.mem (a b : term) : wff := wff{∃ x, |(term.ofSet x).eq a| ∧ |b x|}

macro_rules | `(tm{$t:ident}) => `(term.ofSet $t)
macro_rules | `(wff{$x1:term ∈ $x2:term}) => `(term.mem tm{$x1} tm{$x2})
macro_rules | `(wff{$x1:ident ∈ $x2:term}) => `(term.memSet $x1 tm{$x2})
macro_rules | `(wff{$x1:ident ∈ $x2:ident}) => `(wff.mem $x1 $x2)

axiom is_true : wff → Prop
syntax "⊢{" term "}" : term
macro_rules | `(⊢{$t:term}) => `(is_true wff{$t})
def term.denote : term → Class := fun t x ↦ is_true (t x)
syntax "⊢t{" term "}" : term
macro_rules | `(⊢t{$t:term}) => `(term.denote tm{$t})
@[simp] theorem mem_denote {t : term} {x : set} :
  x ∈ t.denote ↔ is_true (t x) := by rfl

@[simp] axiom wff_mem {x y : set} : ⊢{x ∈ y} ↔ x ∈ y
@[simp] axiom wff_imp {φ ψ : wff} : ⊢{φ → ψ} ↔ ⊢{φ} → ⊢{ψ}
@[simp] axiom wff_neg {φ : wff} : ⊢{¬φ} ↔ ¬⊢{φ}
@[simp] axiom wff_foral {φ : set → wff} : ⊢{∀ x, |φ x|} ↔ ∀ x : set, ⊢{|φ x|}
@[simp] axiom wff_true : ⊢{true}
@[simp] axiom wff_false : ¬⊢{false}
@[simp] theorem wff_and {φ ψ : wff} : ⊢{φ ∧ ψ} ↔ ⊢{φ} ∧ ⊢{ψ} := by simp [wff.and];
@[simp] theorem wff_or {φ ψ : wff} : ⊢{φ ∨ ψ} ↔ ⊢{φ} ∨ ⊢{ψ} :=
  by simp only [wff.or, wff_imp, wff_neg]; exact Iff.symm or_iff_not_imp_left;
@[simp] theorem wff_iff {φ ψ : wff} : ⊢{φ ↔ ψ} ↔ (⊢{φ} ↔ ⊢{ψ}) :=
  by simp only [wff.iff, wff_and, wff_imp]; exact Iff.symm iff_def;
@[simp] theorem wff_exist {φ : set → wff} : ⊢{∃ x, |φ x|} ↔ ∃ x : set, ⊢{|φ x|} :=
  by simp only [wff_neg]; rw [@wff_foral fun x ↦ wff.neg (φ x)]; simp;
@[simp] axiom wff_term {x : set} : ⊢t{x} = x

def satisfy (A : Class) (φ : wff) : Prop :=
  match φ with
  | wff{x ∈ y} => x ∈ A ∧ y ∈ A ∧ x ∈ y
  | wff{¬φ} => ¬(satisfy A φ)
  | wff{φ → ψ} => (satisfy A φ) → (satisfy A ψ)
  | wff.foral f => ∀ x s∈ A, (satisfy A (f x))
  | wff{true} => true
  | wff{false} => false
syntax term "⊨{" term "}" : term
macro_rules | `($A:term ⊨{$t:term}) => `(satisfy $A wff{$t})
def denoteIn (A : Class) (t : term) : Class := fun x => x ∈ A ∧ A⊨{|t x|}
syntax term "⊨t{" term "}" : term
macro_rules | `($A:term ⊨t{$t:term}) => `(denoteIn $A tm{$t})
@[simp] theorem mem_denoteIn {A : Class} {t : term} {x : set} :
  x ∈ denoteIn A t ↔ x ∈ A ∧ A⊨{|t x|} := by rfl

open Lean Elab Term Meta in
private def collectSetFVars (e : Expr) : TermElabM (Array Expr) := do
  let e ← instantiateMVars e
  let (_, s) ← e.collectFVars.run {}
  let setType := Lean.mkConst ``set
  let mut result := #[]
  for fvarId in s.fvarIds do
    let decl ← fvarId.getDecl
    let ty ← instantiateMVars decl.type
    if ← isDefEq ty setType then
      result := result.push (mkFVar fvarId)
  return result
open Lean Elab Term Meta in
private def mkMemExpr (x A : Expr) : TermElabM Expr := do
  mkAppM ``belong #[x, A]
open Lean Elab Term Meta in
private def mkAllMemExpr (A : Expr) (xs : Array Expr) : TermElabM Expr := do
  if xs.isEmpty then
    return Lean.mkConst ``True
  let last := xs.back!
  let mut result ← mkMemExpr last A
  for x in xs.pop.reverse do
    let hx ← mkMemExpr x A
    result := mkApp2 (Lean.mkConst ``And) hx result
  return result

abbrev absolute (A : Class) (φ : wff) := A⊨{φ} ↔ ⊢{φ}
abbrev absolute_tm (A : Class) (φ : term) := A⊨t{|φ|} = ⊢t{|φ|}
theorem uf (h : absolute A φ) : A⊨{φ} ↔ ⊢{φ} := h
theorem uf_tm (h : absolute_tm A φ) : A⊨t{|φ|} = ⊢t{|φ|} := h

syntax:max ident "|abs{" term "}" : term
open Lean Elab Term Meta in elab_rules : term
  | `($A:ident|abs{$t:term}) => do
    -- 1. elaborate A
    let AExpr ← elabTerm A none
    -- 2. 先把原公式 elaboration 成 wff
    let wffStx ← `(wff{$t})
    let φExpr ← elabTermEnsuringType wffStx (some (Lean.mkConst ``wff))
    -- 3. 收集 wff Expr 中真正的 set-valued free variables
    let freeVars ← collectSetFVars φExpr
    -- 4. 构造 free variables ∈ A
    let hExpr ← mkAllMemExpr AExpr freeVars
    -- 5. 构造 absolute A φ
    let absExpr ← mkAppM ``absolute #[AExpr, φExpr]
    -- 6. h → absolute A φ
    return ← mkArrow hExpr absExpr
syntax:max ident "|at{" term "}" : term
open Lean Elab Term Meta in elab_rules : term
  | `($A:ident|at{$t:term}) => do
    -- 1. elaborate A
    let AExpr ← elabTerm A none
    -- 2. 先把原公式 elaboration 成 wff
    let wffStx ← `(tm{$t})
    let φExpr ← elabTermEnsuringType wffStx (some (Lean.mkConst ``term))
    -- 3. 收集 wff Expr 中真正的 set-valued free variables
    let freeVars ← collectSetFVars φExpr
    -- 4. 构造 free variables ∈ A
    let hExpr ← mkAllMemExpr AExpr freeVars
    -- 5. 构造 absolute A φ
    let absExpr ← mkAppM ``absolute_tm #[AExpr, φExpr]
    -- 6. h → absolute A φ
    return ← mkArrow hExpr absExpr

macro_rules | `(wff{$x1:term = $x2:term}) => `(term.eq tm{$x1} tm{$x2})
@[simp] theorem wff_eq {x y : set} : ⊢{x = y} ↔ x = y := by
  unfold term.ofSet term.eq;
  simp only [wff_foral, ↓wff_iff, wff_mem]; exact extensionality_iff;
@[simp] theorem wff_eq_term {x y : term} : ⊢{|x| = |y|} ↔ x.denote = y.denote := by
  unfold term.eq; simp only [wff_foral, wff_iff];
  rw [←extensionality_belong]; simp only [mem_denote];
-- macro_rules | `(tm{{$x:ident // $y:term}}) => `(fun $x ↦ wff{$y})
def term.pair (a b : term) : term := fun x ↦ wff{x = |a| ∨ x = |b|}
macro_rules | `(tm{s{$a:term, $b:term}}) => `(term.pair tm{$a} tm{$b})
@[simp] theorem tm_pair : ⊢t{s{a, b}} = s{a, b} := by
  rw [←extensionality_belong]; intro x; unfold term.denote;
  rw [←set_belong_set_to_class, proof_in_Class];
  unfold term.pair; simp [←set_eq_iff_class];
def term.oneset (a : term) : term := fun x ↦ wff{x = |a|}
macro_rules | `(tm{s{$a:term}}) => `(term.oneset tm{$a})
@[simp] theorem tm_oneset : ⊢t{s{a}} = s{a} := by
  rw [←extensionality_belong]; intro x; unfold term.denote;
  rw [←set_belong_set_to_class, proof_in_Class];
  unfold term.oneset; simp [←set_eq_iff_class];
def term.union (a : term) : term := fun c ↦ wff{∃ x, x ∈ |a| ∧ c ∈ x}
macro_rules | `(tm{∪($a:term)}) => `(term.union tm{$a})
@[simp] theorem tm_union : ⊢t{∪(a)} = ∪(a) := by
  rw [←extensionality_belong];
  simp only [mem_denote, term.union, term.memSet, term.ofSet, wff_neg, wff_foral, wff_and,
    wff_mem, not_and, not_forall, not_not, ← set_belong_set_to_class, has_union.proof_union];
  intro a; simp only [exists_prop, and_comm];
macro_rules | `(wff{$x s⊆ $y}) => `(wff{∀ x, x ∈ $x → x ∈ $y})
macro_rules | `(wff{$x ≠ $y}) => `(wff{¬$x = $y})
def term.empty : term := fun _ ↦ wff{false}
macro_rules | `(tm{s0}) => `(term.empty)
@[simp] theorem tm_empty : ⊢t{s0} = s0 := by
  rw [←extensionality_belong]; intro x; simp [←set_belong_set_to_class, term.empty];
def term.inter (a b : term) : term := fun x ↦ wff{x ∈ |a| ∧ x ∈ |b|}
macro_rules | `(tm{$a ∩ $b}) => `(term.inter tm{$a} tm{$b})
@[simp] theorem tm_inter : ⊢t{a ∩ b} = a ∩ b := by
  rw [←extensionality_belong]; intro x; simp [←set_belong_set_to_class, term.inter];
def term.bunion (a b : term) : term := fun x ↦ wff{x ∈ |a| ∨ x ∈ |b|}
macro_rules | `(tm{$a ∪ $b}) => `(term.bunion tm{$a} tm{$b})
@[simp] theorem tm_bunion : ⊢t{a ∪ b} = a ∪ b := by
  rw [←extensionality_belong]; intro x; simp [←set_belong_set_to_class, term.bunion];

macro_rules | `(wff{Ax1}) => `(wff{∀ a x y, x = y → x ∈ a → y ∈ a})
macro_rules | `(wff{Ax2}) => `(wff{∀ a b, ∃ x, x = s{a, b}})
macro_rules | `(wff{Ax3}) => `(wff{∀ a, ∃ x, x = ∪(a)})
macro_rules | `(wff{Ax4}) => `(wff{∀ a, ∃ x, ∀ y, (y ∈ x ↔ y s⊆ a)})
def Ax5 (φ : set → set → wff) := wff{(∀ a, (∀ u v w, |φ u v| ∧ |φ u w| → v = w) →
  ∃ b, ∀ y, y ∈ b ↔ (∃ x, x ∈ a ∧ |φ x y|))}
macro_rules | `(wff{Ax6}) => `(wff{∀ a, a ≠ s0 → ∃ x, x ∈ a ∧ x ∩ a = s0})

theorem abs_imp : absolute A φ → absolute A ψ → absolute A wff{φ → ψ} := by
  intro h1 h2; simp only [absolute, wff_imp] at *; unfold satisfy; simp [h1, h2];
theorem abs_neg : absolute A φ → absolute A wff{¬φ} := by
  intro h; simp only [absolute, wff_neg] at *; unfold satisfy; simp [h];
@[simp] theorem satisfy_and : satisfy A wff{φ ∧ ψ} ↔ (satisfy A φ ∧ satisfy A ψ) := by
  unfold wff.and; simp [satisfy];
theorem abs_and : absolute A φ → absolute A ψ → absolute A wff{φ ∧ ψ} :=
  fun h1 h2 ↦ abs_neg (abs_imp h1 (abs_neg h2))
@[simp] theorem satisfy_or : satisfy A wff{φ ∨ ψ} ↔ (satisfy A φ ∨ satisfy A ψ) := by
  unfold wff.or; simp only [satisfy]; rw [or_iff_not_imp_left];
theorem abs_or : absolute A φ → absolute A ψ → absolute A wff{φ ∨ ψ} :=
  fun h1 h2 ↦ abs_imp (abs_neg h1) h2
theorem abs_foral_imp {A : Class} {φ ψ : set → wff}
  (h1 : ∀ x s∈ A, absolute A (φ x)) (h2 : ∀ x s∈ A, absolute A (ψ x))
  (hbound : ∀ x, ⊢{|φ x|} → x ∈ A) : absolute A wff{∀ x, |φ x| → |ψ x|} := by
  simp only [absolute, satisfy, wff_foral, wff_imp] at *
  constructor
  · intro h x hxφ; have hxA : x ∈ A := hbound x hxφ;
    have hsφ : satisfy A (φ x) := (h1 x hxA).mpr hxφ;
    have hsψ : satisfy A (ψ x) := h x hxA hsφ;
    exact (h2 x hxA).mp hsψ;
  · intro h x hxA hsφ;
    have htφ : ⊢{|φ x|} := (h1 x hxA).mp hsφ;
    have htψ : ⊢{|ψ x|} := h x htφ;
    exact (h2 x hxA).mpr htψ
@[simp] theorem satisfy_iff : satisfy A wff{φ ↔ ψ} ↔ (satisfy A φ ↔ satisfy A ψ) := by
  unfold wff.iff wff.and;
  simp only [satisfy, Classical.not_imp, not_and, not_not]; rw [←iff_def];
theorem abs_foral_iff {A : Class} {φ ψ : set → wff}
  (h1 : ∀ x s∈ A, absolute A (φ x)) (h2 : ∀ x s∈ A, absolute A (ψ x))
  (hbound1 : ∀ x, ⊢{|φ x|} → x ∈ A) (hbound2 : ∀ x, ⊢{|ψ x|} → x ∈ A)
  : absolute A wff{∀ x, |φ x| ↔ |ψ x|} := by
  simp only [absolute, satisfy, wff_foral, wff_iff, satisfy_iff] at *;
  constructor <;> intro h x;
  · constructor <;> intro f;
    · have f1 := hbound1 _ f; rwa [←h2 _ f1, ←h _ f1, h1 _ f1];
    · have f1 := hbound2 _ f; rwa [←h1 _ f1, h _ f1, h2 _ f1];
  · intro hx; rw [h1 _ hx, h2 _ hx, h];
theorem abs_exists {A : Class} {φ : set → wff}
  (h1 : ∀ x s∈ A, absolute A (φ x))
  (hbound : ∀ x, ⊢{|φ x|} → x ∈ A) : absolute A wff{∃ x, |φ x|} := by
  apply abs_neg; have h1 := fun x fx ↦ abs_neg (h1 x fx);
  unfold absolute; simp only [satisfy, wff_foral, wff_neg];
  unfold absolute at h1; simp only [satisfy, wff_neg] at h1;
  constructor <;> intro h x hx;
  · have h2 := hbound _ hx;
    have h3 := h _ h2; rw [h1 _ h2] at h3; contradiction;
  · rw [h1 _ hx]; exact h _;
theorem abs_iff : absolute A φ → absolute A ψ → absolute A wff{φ ↔ ψ} :=
  fun h1 h2 ↦ abs_and (abs_imp h1 h2) (abs_imp h2 h1)

theorem abs_memset {A : Class} : Tr(A) → A|abs{x ∈ y} := by
  intro h1 ⟨h2, h3⟩; simp only [absolute, satisfy, h2, h3, true_and, wff_mem];
theorem abs_subset {A : Class} {x y : set} : Tr(A) → A|abs{x s⊆ y} := by
  intro h1 ⟨h2, h3⟩; apply abs_foral_imp <;> intro z hz;
  · exact abs_memset h1 ⟨hz, h2⟩;
  · exact abs_memset h1 ⟨hz, h3⟩;
  · simp only [wff_mem] at hz; exact h1 _ h2 _ hz;
theorem abs_eq {A : Class} {x y : set} : Tr(A) → A|abs{x = y} := by
  intro h1 ⟨h2, h3⟩; apply abs_foral_iff <;> intro a ha;
  · exact abs_memset h1 ⟨ha, h2⟩;
  · exact abs_memset h1 ⟨ha, h3⟩;
  · simp only [term.ofSet, wff_mem] at ha; exact h1 _ h2 _ ha;
  · simp only [term.ofSet, wff_mem] at ha; exact h1 _ h3 _ ha;
theorem abs_set_eq_term {A : Class} {x : set} {φ : term}
  (h : ∀ c s∈ A, absolute A (φ c)) (hbound : ∀ x, ⊢{|φ x|} → x ∈ A)
  : Tr(A) → A|abs{x = |φ|} := by
  intro h1 h2; apply abs_foral_iff <;> intro z hz;
  · exact abs_memset h1 ⟨hz, h2⟩;
  · exact h _ hz;
  · simp only [term.ofSet, wff_mem] at hz; exact h1 _ h2 _ hz;
  · exact hbound _ hz;
theorem abs_set_mem_term {A : Class} {x : set} {φ : term} :
  absolute_tm A φ → x ∈ A → (satisfy A (φ x) ↔ is_true (φ x)) := by
  intro h hx; unfold absolute_tm at h; rw [←extensionality_belong] at h;
  have h := h x; rw [mem_denoteIn] at h; simp only [hx, true_and] at h;
  unfold term.denote at h; rwa [proof_in_Class] at h;

theorem abs_set {A : Class} : Tr(A) → A|at{x} := by
  intro h hx; unfold absolute_tm denoteIn; simp only [wff_term];
  rw [←extensionality_belong]; intro a;
  simp only [← set_belong_set_to_class]; rw [proof_in_Class];
  unfold term.ofSet satisfy;
  simp only [hx, true_and, and_self_left, and_iff_right_iff_imp]; exact h _ hx _;
theorem abs_pair {A : Class} : Tr(A) → A|at{s{a, b}} := by
  intro h ⟨ha, hb⟩; rw [absolute_tm, ←extensionality_belong]; intro x;
  simp only [tm_pair, ← set_belong_set_to_class, axiom_of_pair];
  unfold denoteIn; rw [proof_in_Class];
  unfold term.pair; rw [satisfy_or]; constructor <;> intro h1;
  · rcases h1 with ⟨hx, h1⟩;
    rw [uf (abs_eq h ⟨hx, ha⟩), uf (abs_eq h ⟨hx, hb⟩)] at h1;
    simp only [wff_eq] at h1; exact h1;
  have hx : x ∈ A; · cases' h1 <;> subst x <;> assumption;
  use hx; rw [uf (abs_eq h ⟨hx, ha⟩), uf (abs_eq h ⟨hx, hb⟩)];
  simp only [wff_eq]; exact h1;
theorem abs_oneset {A : Class} : Tr(A) → A|at{s{a}} := by
  intro h ha; rw [absolute_tm, ←extensionality_belong]; intro x;
  simp only [mem_denoteIn, term.oneset, tm_oneset, ← set_belong_set_to_class,
    element_in_one_element_set]; rw [←exists_prop];
  conv => lhs; rhs; ext hx; rw [uf (abs_eq h ⟨hx, ha⟩)]; simp [←set_eq_iff_class];
  simp only [exists_prop, and_iff_right_iff_imp]; intro _; subst x; assumption;
theorem abs_mem_term {A : Class} {y : term} : Tr(A) → x ∈ A →
  (A⊨{x ∈ |y|} ↔ x ∈ A⊨t{|y|} ∩ A) := by
  intro h hx; unfold term.memSet denoteIn; simp only [intersection_def];
  rw [proof_in_Class, and_comm]; simp only [and_self_left, iff_and_self];
  intro _; assumption;
theorem abs_term_mem {A : Class} {x y : term} : Tr(A) → (A⊨{|x| ∈ |y|} ↔
  ∃ a : set, a ∈ A⊨t{|y|} ∩ A ∧ ∀ c : set, c ∈ a ↔ c ∈ A⊨t{|x|} ∩ A) := by
  intro h; unfold term.mem satisfy satisfy satisfy;
  simp only [satisfy_and, not_and, not_forall,
    not_not, intersection_comm, intersection_def];
  rw [exists_congr]; intro a; rw [and_assoc, exists_prop];
  apply and_congr_right; intro ha;
  simp only [mem_denoteIn]; unfold term.eq;
  simp only [satisfy, term.ofSet, satisfy_iff, ha, true_and, and_self_left];
  rw [and_comm, exists_prop]; apply and_congr_left; intro h1;
  apply forall_congr'; intro c; rw [←and_congr_right_iff, and_self_left];
  apply iff_congr; · simp only [and_iff_right_iff_imp]; exact h _ ha _;
  rfl;
theorem abs_eq_term {A : Class} {x y : term} : Tr(A) → (A⊨{|x| = |y|} ↔
  ∀ c s∈ A, c ∈ A⊨t{|x|} ↔ c ∈ A⊨t{|y|}) := by
  intro h; unfold term.eq satisfy; apply forall_congr'; intro a;
  apply imp_congr_right; intro ha; simp only [satisfy_iff];
  rw [mem_denoteIn, mem_denoteIn]; simp [ha];
theorem abs_eq_pair {A : Class} {x a b} : Tr(A) → A|abs{x = s{a, b}} := by
  intro h ⟨hx, ha, hb⟩; apply abs_set_eq_term; assumption';
  · intro c hc; exact abs_set_mem_term (abs_pair h ⟨ha, hb⟩) hc;
  · simp only [term.pair, wff_or, wff_eq, forall_eq_or_imp, forall_eq];
    constructor <;> assumption;
theorem abs_eq_oneset {A : Class} {x a} : Tr(A) → A|abs{x = s{a}} := by
  intro h ⟨hx, ha⟩; apply abs_set_eq_term; assumption';
  · intro c hc; exact abs_set_mem_term (abs_oneset h ha) hc;
  · simp only [term.oneset, wff_eq_term, wff_term, ← set_eq_iff_class, forall_eq]; assumption;
theorem abs_union {A : Class} : Tr(A) → A|at{∪(a)} := by
  intro h ha; unfold absolute_tm; rw [←extensionality_belong]; intro x;
  simp only [mem_denoteIn, mem_denote]; unfold term.union satisfy satisfy satisfy;
  simp only [term.memSet, term.ofSet, satisfy_and, not_and, not_forall, not_not,
    wff_neg, wff_foral, wff_and, wff_mem]; rw [←exists_prop];
  conv => lhs; rhs; ext o; rhs; ext; rhs; ext p;
          rw [uf (abs_memset h ⟨p, ha⟩), uf (abs_memset h ⟨o, p⟩)]; simp;
  simp only [exists_prop]; have h1 : ∀ c : set, c ∈ a ↔ (c ∈ A ∧ c ∈ a);
  · simp only [iff_and_self]; exact h _ ha;
  conv => lhs; rhs; rhs; ext; rw [←and_assoc, ←h1];
  simp only [and_iff_right_iff_imp, forall_exists_index, and_imp];
  intro c c1 c2; exact h _ (h _ ha _ c1) _ c2;
theorem abs_eq_union {A : Class} : Tr(A) → A|abs{x = ∪(a)} := by
  intro h2 ⟨hx, ha⟩; apply abs_set_eq_term;
  · intro c hc; exact abs_set_mem_term (abs_union h2 ha) hc;
  · intro d hd; simp only [term.union, wff_neg, wff_foral, ↓wff_and, wff_mem, not_and,
    not_forall, not_not, term.memSet, term.ofSet] at hd; rcases hd with ⟨w, d1, d2⟩;
    exact h2 _ (h2 _ ha _ d1) _ d2;
  assumption';
theorem abs_empty {A : Class} : Tr(A) → A|at{s0} := by
  intro h _; unfold absolute_tm; rw [tm_empty, ←extensionality_belong]; intro x;
  simp [←set_belong_set_to_class, term.empty, satisfy];
theorem abs_eq_empty {A : Class} : Tr(A) → A|abs{x = s0} := by
  intro h2 hx; apply abs_set_eq_term;
  · intro c hc; exact abs_set_mem_term (abs_empty h2 trivial) hc;
  · intro d hd; simp [term.empty] at hd;
  assumption'
theorem abs_bunion {A : Class} : Tr(A) → A|at{a ∪ b} := by
  intro h ⟨ha, hb⟩; unfold absolute_tm; rw [←extensionality_belong]; intro x;
  simp only [mem_denoteIn, term.bunion, term.memSet, term.ofSet, satisfy_or, tm_bunion,
    ← set_belong_set_to_class, binary_union_def]; rw [←exists_prop];
  conv => lhs; rhs; ext hx; rw [uf (abs_memset h ⟨hx, ha⟩), uf (abs_memset h ⟨hx, hb⟩)];
          simp;
  simp only [exists_prop, and_iff_right_iff_imp]; intro hx;
  cases' hx; all_goals apply h; swap; assumption; assumption;
theorem abs_eq_bunion {A : Class} : Tr(A) → A|abs{x = a ∪ b} := by
  intro h2 ⟨hx, ha, hb⟩; apply abs_set_eq_term;
  · intro c hc; exact abs_set_mem_term (abs_bunion h2 ⟨ha, hb⟩) hc;
  · intro d hd; simp only [term.bunion, term.memSet, term.ofSet, wff_or, wff_mem] at hd;
    cases' hd; all_goals apply h2; swap; assumption; assumption;
  assumption';
theorem abs_mem_succ_set {A : Class} : Tr(A) → A|abs{x ∈ a ∪ s{a}} := by
  intro h ⟨hx, ha⟩; unfold absolute; rw [abs_mem_term h hx];
  simp only [intersection_comm, intersection_def, hx, mem_denoteIn, term.bunion, term.memSet,
    term.ofSet, term.oneset, satisfy_or, abs_memset h ⟨hx, ha⟩, wff_mem, true_and, wff_or,
    wff_eq_term, wff_term];
  apply or_congr_right; rw [uf (abs_eq h ⟨hx, ha⟩)]; simp;
theorem abs_eq_succ_set {A : Class} : Tr(A) → A|abs{x = a ∪ s{a}} := by
  intro h ⟨hx, ha⟩; apply abs_set_eq_term;
  · intro c hc; exact abs_mem_succ_set h ⟨hc, ha⟩;
  · intro c hc; simp only [term.bunion, term.memSet, term.ofSet, term.oneset, wff_or, wff_mem,
    wff_eq_term, wff_term, ← set_eq_iff_class] at hc; cases hc with
    | inl hc => exact h _ ha _ hc;
    | inr => subst c; assumption;
  assumption'

def abs_ax1 (A : Class) := A|abs{Ax1}
def abs_ax2 (A : Class) := A|abs{Ax2}
def abs_ax3 (A : Class) := A|abs{Ax3}
def abs_ax4 (A : Class) := A|abs{Ax4}
def abs_ax5 (A : Class) (φ) := A|abs{|Ax5 φ|}
def abs_ax6 (A : Class) := A|abs{Ax6}
theorem abs_axiom1 {A : Class} : Tr(A) → abs_ax1 A := by
  intro h2 _; unfold absolute;
  conv => rhs; simp only [wff_foral, wff_imp, ↓wff_eq, wff_mem, forall_eq', imp_self, implies_true];
  simp only [iff_true];
  have h1 : ∀ x y a, A|abs{x = y → x ∈ a → y ∈ a};
  · intro x y a ⟨hx, hy, ha⟩; apply abs_imp; · exact abs_eq h2 ⟨hx, hy⟩;
    apply abs_imp; · exact abs_memset h2 ⟨hx, ha⟩;
    exact abs_memset h2 ⟨hy, ha⟩;
  unfold absolute at h1; conv at h1 => ext; ext; ext; ext; rhs; simp;
  unfold satisfy satisfy satisfy; intro a ha x hx y hy; apply (h1 x y a ⟨hx, hy, ha⟩).2;
  rw [←set_eq_iff_class]; intro; subst x; simp only [imp_self];
theorem abs_axiom2 {A : Class} : Tr(A) → (abs_ax2 A ↔ ∀ a s∈ A, ∀ b s∈ A, s{a, b} ∈ A) := by
  intro h2; unfold abs_ax2 absolute;
  have hp : ∀ (x x_1 : set), ∃ x_2 : set, ∀ (x_3 : set), x_3 ∈ x_2 ↔ x_3 = x ∨ x_3 = x_1;
  · intro a b; use s{a, b}; exact axiom_of_pair;
  conv => lhs; simp only [forall_const]; rhs; simp only [wff_foral, ↓wff_exist,
          ↓wff_iff, wff_mem, ↓wff_or, ↓wff_eq, hp, implies_true, term.ofSet,
          term.pair, term.eq, extensionality_belong];
  simp only [iff_true];
  unfold satisfy satisfy satisfy satisfy satisfy;
  apply forall_congr'; intro a; apply imp_congr_right; intro ha;
  apply forall_congr'; intro b; apply imp_congr_right; intro hb;
  simp only [not_forall, not_not];
  conv => lhs; rhs; ext; rhs; ext hx; rw [uf (abs_eq_pair h2 ⟨hx, ha, hb⟩)];
  simp [wff_eq_term, ←set_eq_iff_class];
theorem abs_axiom3 {A : Class} : Tr(A) → (abs_ax3 A ↔ ∀ a s∈ A, ∪(a) ∈ A) := by
  intro h2; unfold abs_ax3 absolute;
  simp only [wff_foral, ↓wff_exist, wff_eq_term, wff_term, forall_const];
  conv => lhs; rhs; simp only [tm_union, exists_apply_eq_apply, implies_true];
  simp only [iff_true];
  unfold satisfy satisfy satisfy satisfy; simp only [not_forall, not_not];
  conv => lhs; ext; ext x; rhs; ext; rhs; ext a; rw [uf (abs_eq_union h2 ⟨a, x⟩)];
          simp [←set_eq_iff_class];
  simp [exists_prop];
theorem abs_axiom4 {A : Class} : Tr(A) → (abs_ax4 A ↔ ∀ a s∈ A, P(a) ∩ A ∈ A) := by
  intro h2; unfold abs_ax4 absolute; simp only [wff_foral, ↓wff_exist, wff_iff, wff_mem, wff_imp,
    forall_const];
  conv => lhs; rhs; simp;
  have hp : ∀ (x : set), ∃ x_1 : set, ∀ (x_2 : set), x_2 ∈ x_1 ↔ ∀ (x_3 : set), x_3 ∈ x_2 → x_3 ∈ x
  · intro x; use P(x); simp only [axiom_of_power]; unfold subseteq; simp;
  simp only [hp, implies_true, iff_true];
  unfold satisfy satisfy satisfy satisfy satisfy; simp only [not_forall,
    not_exists, not_not];
  have h1 : ∀ a x y, A|abs{y ∈ x ↔ y s⊆ a};
  · intro a x y ⟨hy, hx, ha⟩; apply abs_iff; · exact abs_memset h2 ⟨hy, hx⟩;
    exact abs_subset h2 ⟨hy, ha⟩;
  unfold absolute at h1;
  conv at h1 => ext; ext; ext; ext; rhs; simp; rw [←subseteq];
  conv => lhs; ext; ext a; rhs; ext; rhs; ext b; ext; ext c; rw [h1 _ _ _ ⟨c, b, a⟩];
  have ht : ∀ x s∈ A, ∀ y : set, y ∈ x ↔ (y ∈ x ∧ y ∈ A);
  · simp only [iff_self_and]; intro x hx y hy; exact h2 _ hx _ hy;
  conv => lhs; ext; ext; rhs; ext; rhs; ext hx; ext; rw [←and_congr_left_iff, ←ht _ hx];
          rw [←axiom_of_power, ←intersection_def]
  conv => lhs; ext; ext; rhs; ext; rhs; ext; rw [extensionality_belong];
  simp;
theorem is_true_axiom5 {φ} : ⊢{|Ax5 φ|} := by
  unfold Ax5;
  simp only [wff_foral, wff_imp, ↓wff_and, ↓wff_eq, ↓wff_exist, wff_iff, wff_mem];
  intro x h; use make_replacement x (fun u v ↦ ⊢{|φ u v|});
  have g := axiom_of_replacement x (fun u v ↦ ⊢{|φ u v|}) h; exact g;
theorem abs_axiom5 {φ} {A : Class} : Tr(A) → (abs_ax5 A φ ↔ ∀ a s∈ A,
  (∀ u s∈ A, ∀ v s∈ A, ∀ w s∈ A, satisfy A (φ u v) ∧ satisfy A (φ u w) → v = w) →
  ((fun x ↦ x ∈ A ∧ ∃ y s∈ a, satisfy A (φ y x)) : Class) ∈ A) := by
  intro h; simp only [abs_ax5, forall_const]; unfold absolute; simp only [is_true_axiom5, iff_true];
  have eq := fun x y ↦ @abs_eq A x y h; unfold absolute at eq; simp only [↓wff_eq, and_imp] at eq;
  conv => lhs; unfold Ax5 satisfy satisfy; ext; ext; lhs; unfold satisfy satisfy satisfy satisfy;
          ext; ext; ext; ext v; ext; ext w; ext z; rw [eq _ _ v w];
  conv => lhs; ext; ext; lhs; ext; ext; ext; ext; ext; ext; lhs; simp only [satisfy,
    Classical.not_imp, not_not];
  apply forall_congr'; intro a; apply imp_congr_right; intro ha; simp only [satisfy_and];
  apply imp_congr_right; intro hu;
  conv => lhs; unfold satisfy satisfy satisfy; simp only [not_forall, Classical.not_imp, not_not];
          rhs; ext; rhs; ext b; unfold satisfy; ext; ext x; rw [satisfy_iff]; unfold satisfy;
          simp only [x, b, true_and];
  conv => rhs; rw [class_belong]; rhs; ext; rhs; ext; rw [proof_in_Class];
  rw [exists_congr]; intro c; rw [exists_prop]; apply and_congr_right; intro hc;
  apply forall_congr'; intro x; have x1 : x ∈ A ∧ x ∈ c ↔ x ∈ c;
  · simp only [and_iff_right_iff_imp]; exact h _ hc _;
  rw [←and_congr_right_iff, x1]; apply iff_congr; · rfl;
  apply and_congr_right; intro hx;
  conv => lhs; unfold satisfy satisfy; simp only [not_forall, Classical.not_imp, not_not];
          rhs; ext d; rhs; ext b; simp [satisfy, b, ha];
  rw [exists_congr]; intro y; rw [exists_prop];
  simp only [and_iff_right_iff_imp, and_imp]; intro y1 _; exact h _ ha _ y1;
theorem abs_axiom6 {A : Class} : Tr(A) → abs_ax6 A := by
  intro h2 _; unfold absolute;
  simp only [wff_foral, wff_imp, wff_neg, wff_eq_term, wff_term, tm_empty, ↓wff_exist, ↓wff_and,
    wff_mem, tm_inter, ←set_eq_iff_class];
  have ax := fun a ↦ @axiom_of_regularity a; simp only [ne_eq, intersection_comm] at ax;
  conv => rhs; ext a; ext h; simp [ax a h];
  simp only [implies_true, iff_true];
  intro x hx; unfold satisfy satisfy;
  have a1 : ∀ x a, A|abs{x ∈ a ∧ x ∩ a = s0};
  · intro x a ⟨hx, ha⟩; apply abs_and (abs_memset h2 ⟨hx, ha⟩); apply abs_foral_iff <;> intro c hc;
    · apply abs_and <;> apply abs_memset h2 <;> constructor <;> assumption;
    · simp [absolute, term.empty, satisfy];
    · simp only [term.inter, term.memSet, term.ofSet, wff_and, wff_mem] at hc; exact h2 _ hx _ hc.1;
    · simp [term.empty] at hc;
  intro ha; unfold absolute at a1; unfold satisfy satisfy;
  simp only [not_forall, not_not];
  conv => rhs; ext; rhs; ext h; rw [a1 _ _ ⟨h, hx⟩]; simp;
  have a2 : ∀ x, A|abs{x ≠ s0};
  · intro x hx; apply abs_neg; exact abs_eq_empty h2 hx;
  unfold absolute satisfy at a2; have a2 := (a2 _ hx).1 ha;
  simp only [wff_neg, wff_eq_term, wff_term, tm_empty, ← set_eq_iff_class] at a2;
  rcases ax _ a2 with ⟨z, x1, x2⟩; use z; use h2 _ hx _ x1; use x1;
  rwa [←set_eq_iff_class];
def term.tr (a : term) : wff := wff{∀ x, x ∈ |a| → x s⊆ |a|}
macro_rules | `(wff{Tr($x)}) => `(term.tr tm{$x})
@[simp] theorem tm_tr : ⊢{Tr(a)} ↔ Tr(a) := by
  simp only [term.tr, term.memSet, term.ofSet, wff_foral, wff_imp, wff_mem]; rfl;
theorem abs_tr {A : Class} : Tr(A) → A|abs{Tr(a)} := by
  intro h ha; apply abs_foral_imp <;> intro x hx;
  · exact abs_memset h ⟨hx, ha⟩;
  · exact abs_subset h ⟨hx, ha⟩;
  · simp only [wff_mem, term.memSet, term.ofSet] at hx; exact h _ ha _ hx;
def term.ord (a : term) : wff := wff{Tr(|a|) ∧ ∀ x, x ∈ |a| → ∀ y, y ∈ |a| → x ∈ y ∨ x = y ∨ y ∈ x}
macro_rules | `(wff{Ord($x)}) => `(term.ord tm{$x})
@[simp] theorem tm_ord : ⊢{Ord(a)} ↔ Ord(a) := by
  simp [term.ord, ←set_eq_iff_class]; rfl;
theorem abs_ord {A : Class} : Tr(A) → A|abs{Ord(a)} := by
  intro h ha; apply abs_and (abs_tr h ha); apply abs_foral_imp <;> intro x hx;
  · exact abs_memset h ⟨hx, ha⟩;
  · apply abs_foral_imp <;> intro y hy;
    · exact abs_memset h ⟨hy, ha⟩;
    · apply abs_or (abs_memset h ⟨hx, hy⟩);
      apply abs_or (abs_eq h ⟨hx, hy⟩); exact abs_memset h ⟨hy, hx⟩;
    · simp only [term.memSet, term.ofSet, wff_mem] at hy; exact h _ ha _ hy;
  simp only [term.memSet, term.ofSet, wff_mem] at hx; exact h _ ha _ hx;
def term.omega : term := fun a ↦ wff{∀ x, x ∈ a ∪ s{a} → Ord(x) ∧ (x = s0 ∨ ∃ y, x = y ∪ s{y})}
macro_rules | `(tm{ω}) => `(term.omega)
@[simp] theorem tm_omega : ⊢t{ω} = ω.val := by
  rw [←extensionality_belong]; intro x;
  simp only [mem_denote, term.omega, term.memSet, term.bunion, term.ofSet, term.oneset, wff_foral,
    wff_imp, wff_or, wff_mem, wff_eq_term, wff_term, ← set_eq_iff_class, wff_and, tm_ord, tm_empty,
    wff_neg, not_forall, not_not, ← set_belong_set_to_class];
  conv => lhs; ext; ext; rhs; rhs; rhs; ext; rw [←extensionality_belong];
          simp [←set_belong_set_to_class, term.bunion, term.oneset, ←set_eq_iff_class];
  have h : x ∈ ω.val ↔ x ∪ s{x} s⊆ K1;
  · rw [ω, axiom_of_infinity]; rw [binary_union_subseteq]; simp only [and_congr_right_iff]; intro h;
    conv => rhs; unfold subseteq; ext; simp only [element_in_one_element_set]; ext a; rw [a];
    simp;
  rw [h]; apply forall_congr'; intro a; simp only [binary_union_def, element_in_one_element_set];
  apply imp_congr_right; intro ha; unfold K1; rw [proof_in_Class];
  have ho : ∀ a h1 o, ⟨a, h1⟩ = succ o ↔ a = succ_set o.val := fun _ _ _ ↦ Subtype.coe_inj.symm;
  conv => rhs; rhs; ext; rhs; rhs; ext; rw [ho];
  have hp : ∀ φ : ordinal → Prop, (∃ x : ordinal, φ x) ↔ (∃ x : set, ∃ h : Ord(x), φ ⟨x, h⟩) :=
    fun φ ↦ Iff.intro (fun ⟨x, h⟩ ↦ ⟨x.val, x.prop, h⟩) (fun ⟨x, h, g⟩ ↦ ⟨⟨x, h⟩, g⟩);
  simp only [exists_prop, and_congr_right_iff]; intro h1; apply or_congr_right; rw [hp];
  apply exists_congr; intro y;
  conv => rhs; rhs; ext; rw [←extensionality_belong];
  simp only [succ_set, binary_union_def, element_in_one_element_set, exists_prop, iff_and_self];
  intro d; have e := d y; simp only [or_true, iff_true] at e; exact ord_element_ord' _ _ h1 e;
theorem abs_mem_omega {A : Class} : Tr(A) → A|abs{a ∈ |tm{ω}|} := by
  intro h ha; unfold term.memSet term.omega; apply abs_foral_imp;
  · intro x hx; simp only [term.memSet, term.bunion, term.ofSet];
    apply abs_or (abs_memset h ⟨hx, ha⟩);
    unfold term.oneset; exact abs_eq h ⟨hx, ha⟩;
  · intro x hx; apply abs_and (abs_ord h hx); apply abs_or (abs_eq_empty h hx);
    unfold absolute satisfy satisfy satisfy; simp only [not_forall, not_not,
      wff_neg, wff_foral, wff_eq_term, wff_term];
    apply exists_congr; intro a2;
    conv => lhs; rhs; ext z; rw [uf (abs_eq_succ_set h ⟨hx, z⟩)]; simp;
    simp only [exists_prop, and_iff_right_iff_imp]; intro c;
    simp only [← extensionality_belong, ← set_belong_set_to_class, mem_denote, term.bunion,
      term.memSet, term.ofSet, term.oneset, wff_or, wff_mem, wff_eq_term, wff_term] at c;
    simp only [extensionality_belong] at c; have c := c a2; simp only [or_true, iff_true] at c;
    exact h _ hx _ c;
  intro x hx; simp only [term.memSet, term.bunion, term.ofSet, term.oneset, wff_or, wff_mem,
    wff_eq_term, wff_term, ← set_eq_iff_class] at hx;
  cases hx with
  | inl hx => exact h _ ha _ hx;
  | inr => subst x; assumption;
theorem abs_eq_omega {A : Class} : Tr(A) → ω s⊆ A → A|abs{a = |tm{ω}|} := by
  intro h h1 ha; apply abs_set_eq_term; assumption'; all_goals intro x hx;;
  · exact abs_mem_omega h hx;
  · have h0 := tm_omega; rw [←extensionality_belong] at h0; have h0 := h0 x;
    simp only [←set_belong_set_to_class, mem_denote] at h0; rw [h0] at hx; exact h1 _ hx;

macro_rules | `(wff{Ax7}) => `(wff{∃ x, x = ω})
def abs_ax7 (A : Class) := A|abs{Ax7}
theorem empty_in_tr {A : Class} : A ≠ s0 → Tr(A) → s0 ∈ A := by
  intro h1 h2; rcases axiom_of_regularity_strong h1 with ⟨x, hx, h3⟩;
  rw [←h3]; convert_to x ∈ A; assumption';
  rw [←extensionality_belong]; simp only [intersection_def, and_iff_left_iff_imp]; exact h2 _ hx;
theorem abs23_omega_ss {A : Class} : A ≠ s0 → Tr(A) → abs_ax2 A → abs_ax3 A → ω s⊆ A := by
  intro h0 h1 h2 h3; apply peano5; use empty_in_tr h0 h1;
  rw [abs_axiom2 h1] at h2; rw [abs_axiom3 h1] at h3;
  intro i hi; convert_to i.val.val ∪ s{i.val.val} ∈ A; · rfl;
  apply h3; apply h2 _ hi; apply h2 _ hi _ hi;
theorem abs_axiom7 {A : Class} : A ≠ s0 → Tr(A) → abs_ax2 A → abs_ax3 A → (abs_ax7 A ↔ ω ∈ A) := by
  intro h0 h1 h2 h3; unfold abs_ax7; simp only [forall_const];
  have h5 := fun a ↦ @abs_eq_omega a _ h1 (abs23_omega_ss h0 h1 h2 h3);
  unfold absolute; have h4 : ⊢{∃ x, x = ω}; · simp;
  simp only [h4, iff_true]; unfold satisfy satisfy satisfy; simp only [not_forall, not_not];
  conv => lhs; rhs; ext; rhs; ext c;
          rw [uf (h5 _ c)]; simp [←set_eq_iff_class];
  simp; rfl;

theorem abs_axiom5_separation {φ : set → wff} {A} : Tr(A) → (∀ ψ, abs_ax5 A ψ) →
  ∀ a s∈ A, {y s∈ a // satisfy A (φ y)} ∈ A := by
  intro h h1 a ha; simp only [abs_axiom5 h] at h1;
  unfold set_separation;
  rw [←set_to_class_belong];
  -- convert_to (fun x ↦ x ∈ A ∧ ∃ y : set, y ∈ a ∧ satisfy A (ψ y x) : Class) ∈ A;
  let ψ : set → set → wff := fun a b ↦ wff{|φ a| ∧ a = b};
  have h1 := h1 ψ a ha; have h2 : _;
  · apply h1; intro u hu v hv w hw ⟨huv, huw⟩; unfold ψ at huv huw;
    rw [satisfy_and, uf (abs_eq h ⟨hu, hv⟩)] at huv;
    simp only [wff_eq_term, wff_term, ←set_eq_iff_class] at huv;
    rw [satisfy_and, uf (abs_eq h ⟨hu, hw⟩)] at huw;
    simp only [wff_eq_term, wff_term, ←set_eq_iff_class] at huw; rw [←huv.2, huw.2];
  convert_to (fun x ↦ x ∈ A ∧ ∃ y : set, y ∈ a ∧ satisfy A (ψ y x) : Class) ∈ A; assumption';
  rw [←extensionality_belong]; intro x; simp only [← set_belong_set_to_class, intersection_def];
  rw [proof_in_Class, proof_in_Class]; unfold ψ;
  conv => rhs; rw [←exists_prop]; rhs; ext x2; rhs; ext; rw [←exists_prop]; rhs; ext a2;
          rw [satisfy_and]; rhs; rw [uf (abs_eq h ⟨h _ ha _ a2, x2⟩)];
          simp only [wff_eq_term, wff_term, ←set_eq_iff_class];
  simp only [exists_and_left, exists_prop, exists_eq_right_right]; rw [and_comm];
  apply and_congr_right; intro _; simp only [iff_and_self]; exact h _ ha _;

def abs_zf (A : Class) := A ≠ s0 ∧ Tr(A) ∧ abs_ax1 A ∧ abs_ax2 A ∧ abs_ax3 A ∧ abs_ax4 A ∧
  (∀ φ, abs_ax5 A φ) ∧ abs_ax6 A ∧ abs_ax7 A

def term.opair (a b : term) : term := tm{s{s{|a|}, s{|a|, |b|}}}
macro_rules | `(tm{s⟨$a, $b⟩}) => `(term.opair tm{$a} tm{$b})
@[simp] theorem tm_opair : ⊢t{s⟨a, b⟩} = s⟨a, b⟩ := by
  rw [←extensionality_belong]; intro x;
  simp only [term.opair, mem_denote, term.pair, wff_or, wff_eq_term, wff_term, tm_oneset,
    ← set_eq_iff_class, tm_pair, make_ordered_pair, pair_comm, ← set_belong_set_to_class,
    axiom_of_pair];
  exact or_comm;
theorem abs_opair : Tr(A) → abs_ax2 A → A|at{s⟨a, b⟩} := by
  intro h h2 ⟨ha, hb⟩; rw [absolute_tm, ←extensionality_belong]; intro x;
  simp only [term.opair, mem_denoteIn, mem_denote];
  conv => lhs; rhs; rhs; arg 0; unfold term.pair;
  simp only [satisfy_or]; rw [abs_axiom2 h] at h2;
  conv => lhs; rw [←exists_prop]; rhs; ext hx; rw [uf (abs_eq_pair h ⟨hx, ha, hb⟩)];
          rw [uf (abs_eq_oneset h ⟨hx, ha⟩)];
  simp only [wff_eq_term, wff_term, tm_oneset, ← set_eq_iff_class, tm_pair, exists_prop, term.pair,
    wff_or, and_iff_right_iff_imp];
  intro hx; cases' hx <;> subst x <;> apply h2 <;> assumption;
theorem abs_eq_opair {A : Class} {x a b} : Tr(A) → abs_ax2 A → A|abs{x = s⟨a, b⟩} := by
  intro h h2 ⟨hx, ha, hb⟩; apply abs_set_eq_term; assumption';
  · intro c hc; exact abs_set_mem_term (abs_opair h h2 ⟨ha, hb⟩) hc;
  · simp only [term.opair, term.pair, wff_or, wff_eq_term, wff_term, tm_oneset, ← set_eq_iff_class,
    tm_pair, forall_eq_or_imp, forall_eq];
    rw [abs_axiom2 h] at h2; constructor <;> apply h2 <;> assumption;

end zfset
