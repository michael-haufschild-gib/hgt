import GaloisForLFunctions.RHTower.XiZerosInfinite
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.PoleHolonomicDegreeBudget

/-!
# The completed-zeta logarithmic derivative is not holonomic

Every zero of `xi` is a simple pole of `xi'/xi`, irrespective of the zero's multiplicity.  The
infinite actual divisor supplied by `XiZerosInfinite`, combined with the general simple-pole
non-holonomicity engine, therefore rules out every polynomial-coefficient linear differential
equation for the completed logarithmic derivative.
-/

open Complex Set Filter Topology Finset Polynomial

namespace RHTower

noncomputable section

/-- At every actual zero, `xi'/xi` has meromorphic order exactly `-1`. -/
theorem meromorphicOrderAt_logDeriv_xi_eq_neg_one {ρ : ℂ} (hzero : xi ρ = 0) :
    meromorphicOrderAt (logDeriv xi) ρ = ((-1 : ℤ) : WithTop ℤ) := by
  have hxi : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)
  have hmne : (analyticOrderAt xi ρ).toNat ≠ 0 := xi_order_toNat_ne_zero hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have horder : analyticOrderAt xi ρ = (k + 1 : ℕ) := by
    calc
      analyticOrderAt xi ρ = ((analyticOrderAt xi ρ).toNat : ℕ∞) :=
        (ENat.coe_toNat (xi_orderAt_ne_top ρ)).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderiv : analyticOrderAt (deriv xi) ρ = k :=
    analyticOrderAt_deriv_of_pos hxi horder
  rw [show logDeriv xi = deriv xi / xi by funext z; rw [logDeriv_apply]; rfl]
  rw [meromorphicOrderAt_div hxi.deriv.meromorphicAt hxi.meromorphicAt,
    hxi.deriv.meromorphicOrderAt_eq, hxi.meromorphicOrderAt_eq, hderiv, horder]
  rw [ENat.map_coe, ENat.map_coe]
  exact_mod_cast (show (k : ℤ) - ((k + 1 : ℕ) : ℤ) = -1 by omega)

noncomputable instance xiDivisorSupport_infinite_inst : Infinite XiDivisorSupport :=
  Set.infinite_coe_iff.mpr xiDivisorSupport_infinite

/-- A chosen injective enumeration of distinct actual `xi` divisor points. -/
def xiZeroEmbedding : ℕ ↪ XiDivisorSupport :=
  Infinite.natEmbedding XiDivisorSupport

/-- The underlying complex point of the chosen `n`-th distinct `xi` zero. -/
def xiZeroPoint (n : ℕ) : ℂ := xiZeroEmbedding n

theorem xiZeroPoint_injective : Function.Injective xiZeroPoint := by
  intro m n h
  exact xiZeroEmbedding.injective (Subtype.ext h)

theorem xiZeroPoint_eq_zero (n : ℕ) : xi (xiZeroPoint n) = 0 :=
  xi_eq_zero_of_mem_divisor_support (xiZeroEmbedding n)

theorem meromorphicAt_logDeriv_xi (ρ : ℂ) : MeromorphicAt (logDeriv xi) ρ := by
  rw [show logDeriv xi = deriv xi / xi by funext z; rw [logDeriv_apply]; rfl]
  exact (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)).deriv.meromorphicAt.div
    (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)).meromorphicAt

/-- **The actual completed-zeta logarithmic derivative is not holonomic.**  If a finite linear
differential relation with polynomial coefficients holds globally, every coefficient is zero. -/
theorem xi_logDeriv_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ Finset.range (n + 1),
      (c j).eval s * iteratedDeriv j (logDeriv xi) s = 0) →
    ∀ j ∈ Finset.range (n + 1), c j = 0 := by
  apply GaloisForLFunctions.not_holonomic_of_meromorphic_simplePoles
    (logDeriv xi) xiZeroPoint xiZeroPoint_injective
    (fun k => meromorphicAt_logDeriv_xi (xiZeroPoint k))
  intro k
  exact meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero k)

/-- **Finite-prefix degree budget at the actual completed divisor.**  Any meromorphic approximant
having genuine simple poles at the first `N` chosen distinct `xi` zeros and satisfying a linear ODE
must spend degree at least `N` in its nonzero leading coefficient.  Increasing differential order
does not reduce this divisor cost. -/
theorem xiZeroPacket_linear_top_natDegree_ge (N : ℕ) (f : ℂ → ℂ)
    (hmero : ∀ k : Fin N, MeromorphicAt f (xiZeroPoint k.val))
    (horder : ∀ k : Fin N,
      meromorphicOrderAt f (xiZeroPoint k.val) = ((-1 : ℤ) : WithTop ℤ))
    (n : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, ∑ j ∈ Finset.range (n + 1),
      (c j).eval s * iteratedDeriv j f s = 0)
    (htop : c n ≠ 0) :
    N ≤ (c n).natDegree := by
  have h := GaloisForLFunctions.card_le_natDegree_linear_top_of_meromorphic_simplePoles
    (ι := Fin N) f (fun k => xiZeroPoint k.val)
    (fun a b hab => Fin.ext (xiZeroPoint_injective hab))
    hmero horder n c hrel htop
  simpa using h

end

end RHTower
