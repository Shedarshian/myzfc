import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal
import Myzfc.ac

namespace zfset
open Lean

inductive wff where
| error
| token (s : Name)
| mem (x1 x2 : wff)
| and (x1 x2 : wff)
| or (x1 x2 : wff)
| imp (x1 x2 : wff)
| iff (x1 x2 : wff)
| neg (x1 : wff)
| foral (x1 : Name) (x2 : wff)
| exist (x1 : Name) (x2 : wff)
deriving Nonempty

syntax:max "wff{" term "}" : term
macro_rules
| `(wff{$t:term}) =>
  match t with
  | `($y:ident) => `(wff.token $(quote y.getId))
  | `($x1:term ∈ $x2:term) => `(wff.mem (wff{$x1}) (wff{$x2}))
  | `($x1:term ∧ $x2:term) => `(wff.and (wff{$x1}) (wff{$x2}))
  | `($x1:term ∨ $x2:term) => `(wff.or (wff{$x1}) (wff{$x2}))
  | `($x1:term → $x2:term) => `(wff.imp (wff{$x1}) (wff{$x2}))
  | `($x1:term ↔ $x2:term) => `(wff.iff (wff{$x1}) (wff{$x2}))
  | `(¬ $x1:term) => `(wff.neg (wff{$x1}))
  | `(($x1:term)) => `(wff{$x1})
  | `(∀ $x1:ident : set, $x2:term) => `(wff.foral $(quote x1.getId) (wff{$x2}))
  | `(∀ $x1:ident* : set, $x2:term) => do
      let init ← `(wff{$x2})
      x1.foldlM (fun x acc ↦ `(wff.foral $(quote x.getId) ($acc))) init
  | `(∃ $x1:ident : set, $x2:term) => `(wff.exist $(quote x1.getId) (wff{$x2}))
  | _ => `(wff.error)

def from_wff (a : wff) : MacroM (TSyntax `term) :=
  match a with
  | wff.token s => do let stx := mkIdent s; `($stx)
  | wff.mem x1 x2 => do `($(← from_wff x1):term ∈ $(← from_wff x2):term)
  | wff.and x1 x2 => do `($(← from_wff x1):term ∧ $(← from_wff x2):term)
  | wff.or x1 x2 => do `($(← from_wff x1):term ∨ $(← from_wff x2):term)
  | wff.imp x1 x2 => do `($(← from_wff x1):term → $(← from_wff x2):term)
  | wff.iff x1 x2 => do `($(← from_wff x1):term ↔ $(← from_wff x2):term)
  | wff.neg x1 => do `(¬ $(← from_wff x1):term)
  | wff.foral x1 x2 => do let stx := mkIdent x1; `(∀ $stx : set, $(← from_wff x2):term)
  | wff.exist x1 x2 => do let stx := mkIdent x1; `(∃ $stx:ident : set, $(← from_wff x2):term)
  | wff.notmem x1 x2 => do `($(← from_wff x1):term ∉ $(← from_wff x2):term)
  | wff.error => Macro.throwError "cannot convert wff.error to syntax"
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
--   | wff.error => Macro.throwError "cannot convert wff.error to syntax"

end zfset
