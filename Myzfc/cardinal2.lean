import Mathlib
import Myzfc.zfcset1
import Myzfc.zfcset2
import Myzfc.ordinals
import Myzfc.cardinal
import Myzfc.ac

namespace zfset

def limit_point (x : set) (α : ordinal) := ∪(x ∩ α) = α.val
def unbounded_sset (c : set) (κ : cardinal) := c s⊆ κ.val ∧ ∀ α o∈ κ.val, ∃ β o∈ c, α < β
def close_sset (c : set) (κ : cardinal) := c s⊆ κ.val ∧ ∀ α o∈ κ.val, limit_point c α → α ∈ c
def close_unbound_sset (c : set) (κ : cardinal) := unbounded_sset c κ ∧ close_sset c κ
def stationary_sset (s : set) (κ : cardinal) := s s⊆ κ.val ∧
    ∀ c : set, close_unbound_sset c κ → s ∩ c ≠ s0
def mahlo (α : ordinal) := inaccessible α ∧ stationary_sset
  {ℵ_(γ).val.val // γ o∈ α // regular γ} ℵ_(α)



end zfset
