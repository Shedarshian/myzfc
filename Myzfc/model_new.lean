import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal
import Myzfc.ac

namespace zfset
open Lean

inductive wff where
| mem (x1 x2 : Name)
| and (x1 x2 : wff)
| or (x1 x2 : wff)
| imp (x1 x2 : wff)
| iff (x1 x2 : wff)
| neg (x1 : wff)
| foral (x1 : Name) (x2 : wff)
| exist (x1 : Name) (x2 : wff)

syntax "∀" "${" explicitBinders "}" ", " term : term
syntax "${" term "}" : term
syntax:max "wff{" term "}" : term
macro_rules
| `(wff{$t:term}) =>
  match t with
  | `($y:ident) =>
    let s := y.getId.eraseMacroScopes.toString
    if s.front.isLower then
      `($(quote y.getId))
    else
      `($y)
  | `($x1:term ∈ $x2:term) => `(wff.mem (wff{$x1}) (wff{$x2}))
  | `($x1:term ∧ $x2:term) => `(wff.and (wff{$x1}) (wff{$x2}))
  | `($x1:term ∨ $x2:term) => `(wff.or (wff{$x1}) (wff{$x2}))
  | `($x1:term → $x2:term) => `(wff.imp (wff{$x1}) (wff{$x2}))
  | `($x1:term ↔ $x2:term) => `(wff.iff (wff{$x1}) (wff{$x2}))
  | `(¬ $x1:term) => `(wff.neg (wff{$x1}))
  | `(($x1:term)) => `((wff{$x1}))
  | `(∀ $x1:ident, $x2:term) => `(wff.foral $(quote x1.getId) (wff{$x2}))
  | `(∀ $x1:ident*, $x2:term) => do
      let init ← `(wff{$x2})
      x1.foldlM (fun x acc ↦ `(wff.foral $(quote x.getId) ($acc))) init
  | `(∃ $x1:ident, $x2:term) => `(wff.exist $(quote x1.getId) (wff{$x2}))
  | `(${$y:ident}) => `($y)
  | `(∀ ${$x1:ident}, $x2:term) => `(wff.foral $x1 (wff{$x2}))
  | t => Lean.Macro.throwError s!"syntax '{t}' is not defined"

def change_name (φ : wff) (x a : Name) :=
match φ with
| wff.mem y z => wff.mem (if y = x then a else y) (if z = x then a else z)
| wff.foral y ψ => if y = x then (wff.foral y ψ) else (wff.foral y (change_name ψ x a))
| wff.exist y ψ => if y = x then (wff.exist y ψ) else (wff.exist y (change_name ψ x a))
| wff.and φ1 φ2 => wff.and (change_name φ1 x a) (change_name φ2 x a)
| wff.or φ1 φ2 => wff.or (change_name φ1 x a) (change_name φ2 x a)
| wff.imp φ1 φ2 => wff.imp (change_name φ1 x a) (change_name φ2 x a)
| wff.iff φ1 φ2 => wff.iff (change_name φ1 x a) (change_name φ2 x a)
| wff.neg φ => wff.neg (change_name φ x a)
syntax:max term "[" term " ↦ " term "]" : term
macro_rules
| `($φ[$x ↦ $a]) => `(change_name $φ $x $a)
def nf (φ : wff) (x : Name) : Except Nat wff :=
match φ with
| wff.mem y z => if y = x ∨ z = x then throw 1 else return wff.mem y z
| wff.foral y ψ =>
  do if y = x then return wff.foral y ψ else let px ← (nf ψ x); return wff.foral y px
| wff.exist y ψ =>
  do if y = x then return wff.exist y ψ else let px ← (nf ψ x); return wff.exist y px
| wff.and φ1 φ2 => do let px ← (nf φ1 x); let py ← (nf φ2 x); return wff.and px py
| wff.or φ1 φ2 => do let px ← (nf φ1 x); let py ← (nf φ2 x); return wff.or px py
| wff.imp φ1 φ2 => do let px ← (nf φ1 x); let py ← (nf φ2 x); return wff.imp px py
| wff.iff φ1 φ2 => do let px ← (nf φ1 x); let py ← (nf φ2 x); return wff.iff px py
| wff.neg φ => do let px ← (nf φ x); return wff.neg px
syntax "#nf{" term "," ident "}" : term
macro_rules
| `(#nf{$φ, $x}) => `(nf $φ $x)

axiom is_true : wff → Prop
syntax "⊢{" term "}" : term
macro_rules
| `(⊢{$t:term}) => `(is_true wff{$t})

@[simp] axiom wff_and {φ ψ : wff} : ⊢{φ ∧ ψ} ↔ ⊢{φ} ∧ ⊢{ψ}
@[simp] axiom wff_or {φ ψ : wff} : ⊢{φ ∨ ψ} ↔ ⊢{φ} ∨ ⊢{ψ}
@[simp] axiom wff_imp {φ ψ : wff} : ⊢{φ → ψ} ↔ ⊢{φ} → ⊢{ψ}
@[simp] axiom wff_iff {φ ψ : wff} : ⊢{φ ↔ ψ} ↔ (⊢{φ} ↔ ⊢{ψ})
@[simp] axiom wff_neg {φ : wff} : ⊢{¬φ} ↔ ¬⊢{φ}
axiom wff_a4 {x a : Name} {φ : wff} : ⊢{∀ ${x}, φ} → is_true φ[x ↦ a]
axiom wff_a5 {x : Name} {φ ψ : wff} : ⊢{∀ ${x}, (φ → ψ)} → ⊢{(∀ ${x}, φ) → (∀ ${x}, ψ)}
axiom wff_a6 {x : Name} {φ : wff} : ⊢{φ} → ⊢{∀ ${x}, φ}

lemma hilbert1 {φ ψ : wff} : ⊢{φ → ψ → φ} := by
  simp only [wff_imp]; exact fun a b ↦ a;
lemma test {φ : wff} : ⊢{φ} → ⊢{∀ t, φ} := wff_a6
lemma test2 : ⊢{∀ x, x ∈ a ∧ c ∈ x} → ⊢{b ∈ a ∧ c ∈ b} := wff_a4
lemma test3 : ⊢{∀ x, x ∈ ${a} ∧ c ∈ x} → ⊢{b ∈ ${a} ∧ c ∈ b} := wff_a4
lemma test4 : ⊢{∀ ${x}, ${x} ∈ ${x}} → ⊢{a ∈ a} := @wff_a4 x _ (wff.mem x x)
lemma nf1 : is_true #nf{wff{x ∈ y}, z}

end zfset
