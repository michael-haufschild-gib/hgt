import GaloisForLFunctions.BiScaleUncertainty.SieveResonantVisibility
import GaloisForLFunctions.BiScaleUncertainty.SieveRawMomentPerturbation

/-! Exact prime-factor-width threshold for factorial-period visibility. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
set_option autoImplicit false

/-- Primary frequencies give an actual visibility word whenever the width is at most five. -/
theorem visible_of_width_le_five (N q : ℕ) (hq : q ∈ Icc 1 N)
    (hw : q.primeFactors.card ≤ 5) : Visible N (primePowerOrders N) q := by
  classical
  let r : q.primeFactors → ZMod N.factorial :=
    fun p => ((N.factorial/((p : ℕ)^q.factorization p) : ℕ) : ZMod N.factorial)
  have hr (p : q.primeFactors) : addOrderOf (r p) = (p : ℕ)^q.factorization p :=
    frequency_order (mem_filter.mp (primary_order_mem N q hq p)).1
  have hord : addOrderOf (∑ p, r p) = q := by
    calc
      _ = ∏ p, addOrderOf (r p) := by
        apply order_sum_of_pairwise_coprime
        intro p _ u _ hpu
        rw [hr p, hr u]
        exact Nat.pairwise_coprime_pow_primeFactors_factorization hpu
      _ = ∏ p : q.primeFactors, (p : ℕ)^q.factorization p :=
        prod_congr rfl (fun p _ => hr p)
      _ = q := (Nat.prod_primeFactors_coe_pow_factorization
        (show q ≠ 0 from (Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hq).1).ne')).symm
  have h1 : 1 ∈ primePowerOrders N := by
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨le_refl _, ?_⟩, by simp⟩
    exact (mem_Icc.mp hq).1.trans (mem_Icc.mp hq).2
  exact visible_from_small_family N q _ h1 r (by simpa using hw) hord
    (fun p => by rw [hr p]; exact primary_order_mem N q hq p)

/-- Exact arithmetic threshold for first-order visibility in the prime-power source. -/
theorem prime_power_visibility_iff (N q : ℕ) (hq : q ∈ Icc 1 N) :
    Visible N (primePowerOrders N) q ↔ q.primeFactors.card ≤ 5 :=
  ⟨width_le_five_of_visible N q, visible_of_width_le_five N q hq⟩

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
