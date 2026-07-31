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
  inaccessible α ∧ stationary_sset {ℵ_(γ).val o// γ o∈ α // regular γ} ℵ_(α)



end zfset
