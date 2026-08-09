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

syntax:max "wff{" term "}" : term
macro_rules | `(wff{$t:ident}) => `($t)
macro_rules | `(wff{$x1:term ∈ $x2:term}) => `(wff{∃ x, x = $x1 ∧ x ∈ $x2})
macro_rules | `(wff{$x1:ident ∈ $x2:ident}) => `(wff.mem $x1 $x2)
macro_rules | `(wff{$x1:term → $x2:term}) => `(wff.imp (wff{$x1}) (wff{$x2}))
macro_rules | `(wff{¬$x1:term}) => `(wff.neg (wff{$x1}))
macro_rules | `(wff{$x1:term ∧ $x2:term}) => `(wff{¬($x1 → ¬$x2)})
macro_rules | `(wff{$x1:term ∨ $x2:term}) => `(wff{¬$x1 → $x2})
macro_rules | `(wff{$x1:term ↔ $x2:term}) => `(wff{($x1 → $x2) ∧ ($x2 → $x1)})
macro_rules | `(wff{($x1:term)}) => `((wff{$x1}))
macro_rules | `(wff{∀ $x1:ident, $x2:term}) => `(wff.foral (fun $x1 ↦ wff{$x2}))
macro_rules | `(wff{∀ $x1:ident*, $x2:term}) => do
      let init ← `(wff{$x2})
      let r ← x1.foldrM (fun x (acc : TSyntax `term) ↦ `(wff.foral (fun $x ↦ ($acc)))) init
      return r.raw
macro_rules | `(wff{∃ $x1:ident, $x2:term}) => `(wff{¬∀ $x1, ¬$x2})
macro_rules | `(wff{|$x|}) => `($x)
macro_rules | `(wff{true}) => `(wff.True)
macro_rules | `(wff{false}) => `(wff.False)

axiom is_true : wff → Prop
syntax "⊢{" term "}" : term
macro_rules | `(⊢{$t:term}) => `(is_true wff{$t})

@[simp] axiom wff_mem {x y : set} : ⊢{x ∈ y} ↔ x ∈ y
@[simp] axiom wff_imp {φ ψ : wff} : ⊢{φ → ψ} ↔ ⊢{φ} → ⊢{ψ}
@[simp] axiom wff_neg {φ : wff} : ⊢{¬φ} ↔ ¬⊢{φ}
@[simp] axiom wff_foral {φ : set → wff} : ⊢{∀ x, |φ x|} ↔ ∀ x : set, ⊢{|φ x|}
@[simp↓ 110] theorem wff_and {φ ψ : wff} : ⊢{φ ∧ ψ} ↔ ⊢{φ} ∧ ⊢{ψ} := by simp;
@[simp↓ 110] theorem wff_or {φ ψ : wff} : ⊢{φ ∨ ψ} ↔ ⊢{φ} ∨ ⊢{ψ} :=
  by simp only [wff_imp, wff_neg]; exact Iff.symm or_iff_not_imp_left;
@[simp↓ 120] theorem wff_iff {φ ψ : wff} : ⊢{φ ↔ ψ} ↔ (⊢{φ} ↔ ⊢{ψ}) :=
  by simp only [wff_and, wff_imp]; exact Iff.symm iff_def;
@[simp↓ 110] theorem wff_exist {φ : set → wff} : ⊢{∃ x, |φ x|} ↔ ∃ x : set, ⊢{|φ x|} :=
  by simp only [wff_neg]; rw [@wff_foral fun x ↦ wff.neg (φ x)]; simp;

lemma hilbert1 {φ ψ : wff} : ⊢{φ → ψ → φ} := by
  simp only [wff_imp]; exact fun a b ↦ a;
lemma test : ⊢{∀ x, x ∈ a} ↔ ∀ y, ⊢{y ∈ a} := @wff_foral (fun t ↦ wff{t ∈ a})

macro_rules | `(wff{$x1:term = $x2:term}) => `(wff{∀ x, x ∈ $x1 ↔ x ∈ $x2})
@[simp↓ 130] theorem wff_eq {x y : set} : ⊢{x = y} ↔ x = y := by
  simp only [wff_foral, ↓wff_iff, wff_mem]; exact extensionality_iff;
macro_rules | `(wff{$a:ident ∈ {$x:ident // $y:term}}) => `((fun $x ↦ wff{$y}) $a)
macro_rules | `(wff{$x:ident ∈ s{$a:term, $b:term}}) => `(wff{$x ∈ $a ∨ $x ∈ $b})
macro_rules | `(wff{$x:ident ∈ ∪($a:term)}) => `(wff{∃ x, x ∈ $a ∧ $x ∈ x})
macro_rules | `(wff{$x s⊆ $y}) => `(wff{∀ x, x ∈ $x → x ∈ $y})
macro_rules | `(wff{$x ≠ $y}) => `(wff{¬$x = $y})
macro_rules | `(wff{$_:ident ∈ s0}) => `(wff.False)
macro_rules | `(wff{$x:ident ∈ $a ∩ $b}) => `(wff{$x ∈ $a ∧ $x ∈ $b})

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

def freevar (φ : wff) : List set := sorry
def absolute (A : Class) (φ : wff) := A⊨{φ} ↔ ⊢{φ}
syntax:max "|" ident "(" ident,* ")abs{" term "}" : term
macro_rules
| `(|$A:ident($xs:ident,*)abs{$t:term}) => do
  let h ← mkAllMem A xs.getElems; `($h → (absolute $A wff{$t}))

def Ax1 := wff{∀ a x y, x = y → x ∈ a → y ∈ a}
noncomputable def Ax2 := wff{∀ a b, ∃ x, x = s{a, b}}
noncomputable def Ax3 := wff{∀ a, ∃ x, x = ∪(a)}
def Ax4 := wff{∀ a, ∃ x, ∀ y, (y ∈ x ↔ y s⊆ a)}
def Ax6 := wff{∀ a, a ≠ s0 → ∃ x, x ∈ a ∧ x ∩ a = s0}

theorem abs_in {A : Class} : Tr(A) → |A(x,y)abs{x ∈ y} := by
  intro h1 ⟨h2, h3⟩; simp only [absolute, satisfy, h2, h3, true_and, wff_mem];


end zfset
