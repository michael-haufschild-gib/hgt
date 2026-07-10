/-
A Mertens-type lower bound for the prime-harmonic sum, and square-root log-log growth of the
all-prime Sonin Euler boundary sums.

Unique factorization dominates the harmonic sum by the finite Euler product over the primes
below the cutoff: every integer up to `X` is `(X+1)`-smooth, so the geometric Euler product
identity bounds `∑_{m ≤ X} m⁻¹` by `∏_{p ≤ X} (1 - p⁻¹)⁻¹`. Taking logarithms, bounding each
factor by `log t ≤ t - 1`, and removing the telescoping second-order tail leaves

`log log (X+1) - 1 ≤ ∑_{p ≤ X} p⁻¹`.

Combined with the compact-distance lower bound for finite prime families of archimedean Euler
corners, the canonical all-prime boundary sums keep distance at least `√(log log (X+1) - 1)`
from every compact operator: the essential norm of the unsmoothed all-prime Euler seam grows
at least like the square root of the double logarithm of the cutoff.
-/
import GaloisForLFunctions.RHTower.SoninCalkinNormBound
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

namespace RHTower

open Finset

/-! ### The finite Euler product dominates the harmonic sum -/

private def natInvHom : ℕ →* ℝ where
  toFun n := ((n : ℝ))⁻¹
  map_one' := by norm_num
  map_mul' m n := by push_cast; rw [mul_inv]

@[simp] private theorem natInvHom_apply (n : ℕ) : natInvHom n = ((n : ℝ))⁻¹ := rfl

theorem harmonic_sum_le_prod_primesBelow (X : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ ≤
      ∏ p ∈ Nat.primesBelow (X + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
  have hf : ∀ {p : ℕ}, p.Prime → ‖natInvHom p‖ < 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    rw [natInvHom_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hgeom := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natInvHom) hf (X + 1)).2
  have hmem : ∀ m ∈ Finset.Icc 1 X, m ∈ (X + 1).smoothNumbers := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    refine Nat.mem_smoothNumbers'.mpr fun p hp hdvd => ?_
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  let e : {m // m ∈ Finset.Icc 1 X} ↪ (X + 1).smoothNumbers :=
    ⟨fun m => ⟨m.1, hmem m.1 m.2⟩, fun x y hxy => Subtype.ext (Subtype.mk_eq_mk.mp hxy)⟩
  have hle := sum_le_hasSum ((Finset.Icc 1 X).attach.map e)
    (fun i _ => by rw [natInvHom_apply]; positivity) hgeom
  have hcongr : ∑ i ∈ (Finset.Icc 1 X).attach.map e, natInvHom (i : ℕ) =
      ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ := by
    rw [Finset.sum_map]
    calc ∑ m ∈ (Finset.Icc 1 X).attach, natInvHom ((e m : (X + 1).smoothNumbers) : ℕ)
        = ∑ m ∈ (Finset.Icc 1 X).attach, (((m : ℕ) : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun m _ => rfl
      _ = ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ :=
          Finset.sum_attach (Finset.Icc 1 X) fun n => ((n : ℝ))⁻¹
  rw [← hcongr]
  exact hle

private theorem sum_Icc_second_order_telescope (X : ℕ) (hX : 1 ≤ X) :
    ∑ m ∈ Finset.Icc 2 X, (((m : ℝ) - 1) * (m : ℝ))⁻¹ = 1 - ((X : ℝ))⁻¹ := by
  induction X with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have hn : n = 0 := by omega
      subst hn
      simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih h1]
      have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have hn0 : (n : ℝ) ≠ 0 := by linarith
      have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith
      push_cast
      have hmid : ((n : ℝ) + 1 - 1) * ((n : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) := by ring
      rw [hmid]
      field_simp
      ring

theorem sum_primesBelow_second_order_le_one (X : ℕ) :
    ∑ p ∈ Nat.primesBelow (X + 1), (((p : ℝ) - 1) * (p : ℝ))⁻¹ ≤ 1 := by
  have hsub : Nat.primesBelow (X + 1) ⊆ Finset.Icc 2 X := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesBelow hp).two_le,
      Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)⟩
  have hmono : ∑ p ∈ Nat.primesBelow (X + 1), (((p : ℝ) - 1) * (p : ℝ))⁻¹ ≤
      ∑ m ∈ Finset.Icc 2 X, (((m : ℝ) - 1) * (m : ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
    have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have h1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    positivity
  rcases Nat.lt_or_ge X 1 with h0 | h1
  · have hX : X = 0 := by omega
    subst hX
    refine hmono.trans ?_
    simp
  · rw [sum_Icc_second_order_telescope X h1] at hmono
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast h1
    have hinv : (0 : ℝ) ≤ ((X : ℝ))⁻¹ := by positivity
    linarith

/-- **Mertens-type lower bound.** The prime-harmonic sum over the primes up to `X` is at
least `log log (X+1) - 1`. -/
theorem log_log_sub_one_le_sum_primesBelow_inv (X : ℕ) (hX : 1 ≤ X) :
    Real.log (Real.log ((X : ℝ) + 1)) - 1 ≤
      ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ := by
  have hX2 : (2 : ℝ) ≤ (X : ℝ) + 1 := by
    have h1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlogpos : 0 < Real.log ((X : ℝ) + 1) := Real.log_pos (by linarith)
  have hp2 : ∀ p ∈ Nat.primesBelow (X + 1), (2 : ℝ) ≤ (p : ℝ) := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
  have hfactorpos : ∀ p ∈ Nat.primesBelow (X + 1), (0 : ℝ) < (1 - ((p : ℝ))⁻¹)⁻¹ := by
    intro p hp
    have h2 := hp2 p hp
    have hlt : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have hpos : 0 < 1 - ((p : ℝ))⁻¹ := by linarith
    positivity
  have hharm : Real.log ((X : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ := by
    have h1 : Real.log ((X : ℝ) + 1) ≤ ((harmonic X : ℚ) : ℝ) := by
      have h := log_add_one_le_harmonic X
      have hcast : ((X : ℝ) + 1) = (((X + 1 : ℕ)) : ℝ) := by push_cast; ring
      rw [hcast]
      exact_mod_cast h
    have h2 : ((harmonic X : ℚ) : ℝ) = ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    linarith [h1, h2.le, h2.ge]
  have hprod_ge : Real.log ((X : ℝ) + 1) ≤
      ∏ p ∈ Nat.primesBelow (X + 1), (1 - ((p : ℝ))⁻¹)⁻¹ :=
    hharm.trans (harmonic_sum_le_prod_primesBelow X)
  have hlogle : Real.log (Real.log ((X : ℝ) + 1)) ≤
      Real.log (∏ p ∈ Nat.primesBelow (X + 1), (1 - ((p : ℝ))⁻¹)⁻¹) :=
    Real.log_le_log hlogpos hprod_ge
  have hlogprod : Real.log (∏ p ∈ Nat.primesBelow (X + 1), (1 - ((p : ℝ))⁻¹)⁻¹) =
      ∑ p ∈ Nat.primesBelow (X + 1), Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) :=
    Real.log_prod fun p hp => (hfactorpos p hp).ne'
  have hterm : ∀ p ∈ Nat.primesBelow (X + 1),
      Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) ≤ ((p : ℝ))⁻¹ + (((p : ℝ) - 1) * (p : ℝ))⁻¹ := by
    intro p hp
    have h2 := hp2 p hp
    have hpne : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hform : (1 - ((p : ℝ))⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
      have hbase : 1 - ((p : ℝ))⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by
        field_simp
      rw [hbase, inv_div]
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (p : ℝ) / ((p : ℝ) - 1) by positivity)
    have hval : (p : ℝ) / ((p : ℝ) - 1) - 1 = ((p : ℝ))⁻¹ + (((p : ℝ) - 1) * (p : ℝ))⁻¹ := by
      field_simp
      ring
    rw [hform]
    linarith [hlog, hval.le, hval.ge]
  have hsum_le : ∑ p ∈ Nat.primesBelow (X + 1), Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) ≤
      ∑ p ∈ Nat.primesBelow (X + 1), (((p : ℝ))⁻¹ + (((p : ℝ) - 1) * (p : ℝ))⁻¹) :=
    Finset.sum_le_sum hterm
  have hsplit : ∑ p ∈ Nat.primesBelow (X + 1), (((p : ℝ))⁻¹ + (((p : ℝ) - 1) * (p : ℝ))⁻¹) =
      ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ +
        ∑ p ∈ Nat.primesBelow (X + 1), (((p : ℝ) - 1) * (p : ℝ))⁻¹ :=
    Finset.sum_add_distrib
  have htail := sum_primesBelow_second_order_le_one X
  have hchain : Real.log (Real.log ((X : ℝ) + 1)) ≤
      ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ + 1 := by
    calc Real.log (Real.log ((X : ℝ) + 1)) ≤
        Real.log (∏ p ∈ Nat.primesBelow (X + 1), (1 - ((p : ℝ))⁻¹)⁻¹) := hlogle
      _ = ∑ p ∈ Nat.primesBelow (X + 1), Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) := hlogprod
      _ ≤ ∑ p ∈ Nat.primesBelow (X + 1), (((p : ℝ))⁻¹ + (((p : ℝ) - 1) * (p : ℝ))⁻¹) := hsum_le
      _ = ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ +
            ∑ p ∈ Nat.primesBelow (X + 1), (((p : ℝ) - 1) * (p : ℝ))⁻¹ := hsplit
      _ ≤ ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ + 1 := by linarith
  linarith

/-! ### Enumeration of the primes below a bound -/

/-- A canonical enumeration of the primes below `N`. -/
def primesBelowEnum (N : ℕ) : Fin (Nat.primesBelow N).card → ℕ :=
  fun i => ((Nat.primesBelow N).equivFin.symm i : ℕ)

theorem primesBelowEnum_mem (N : ℕ) (i : Fin (Nat.primesBelow N).card) :
    primesBelowEnum N i ∈ Nat.primesBelow N :=
  ((Nat.primesBelow N).equivFin.symm i).2

theorem primesBelowEnum_prime (N : ℕ) (i : Fin (Nat.primesBelow N).card) :
    (primesBelowEnum N i).Prime :=
  Nat.prime_of_mem_primesBelow (primesBelowEnum_mem N i)

theorem primesBelowEnum_injective (N : ℕ) : Function.Injective (primesBelowEnum N) := by
  intro i j hij
  exact (Nat.primesBelow N).equivFin.symm.injective (Subtype.ext hij)

theorem one_lt_primesBelowEnum_real (N : ℕ) (i : Fin (Nat.primesBelow N).card) :
    (1 : ℝ) < ((primesBelowEnum N i : ℕ) : ℝ) := by
  exact_mod_cast (primesBelowEnum_prime N i).one_lt

theorem sum_primesBelowEnum {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ i, f (primesBelowEnum N i) = ∑ p ∈ Nat.primesBelow N, f p := by
  rw [← Finset.sum_coe_sort (Nat.primesBelow N) f]
  exact Equiv.sum_comp (Nat.primesBelow N).equivFin.symm fun x => f (x : ℕ)

/-! ### Square-root log-log growth of the all-prime Euler boundary sums -/

/-- **Square-root log-log growth.** The canonical sum of the literal archimedean Euler corners
over all primes up to `X` keeps distance at least `√(log log (X+1) - 1)` from every compact
operator. -/
theorem sqrt_log_log_sub_one_le_norm_sum_primesBelow_eulerCorners_sub_compact
    (a : ℝ) (ha : 0 < a) (X : ℕ) (hX : 1 ≤ X)
    (K : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) (hK : IsCompactOperator K) :
    Real.sqrt (Real.log (Real.log ((X : ℝ) + 1)) - 1) ≤
      ‖(∑ p ∈ Nat.primesBelow (X + 1), archimedeanPrimeEulerCorner a (p : ℝ)) - K‖ := by
  have hlow := finitePrimeReciprocalL2Norm_le_norm_archimedeanEulerCorners_sub_compact
    a ha (primesBelowEnum (X + 1)) (primesBelowEnum_prime (X + 1))
    (primesBelowEnum_injective (X + 1)) K hK
  have hop : finiteArchimedeanPrimeEulerCorners a
      (fun i => ((primesBelowEnum (X + 1) i : ℕ) : ℝ))
      (fun i => one_lt_primesBelowEnum_real (X + 1) i) (fun _ => 1) =
      ∑ p ∈ Nat.primesBelow (X + 1), archimedeanPrimeEulerCorner a (p : ℝ) := by
    rw [finiteArchimedeanPrimeEulerCorners]
    simp only [one_smul]
    exact sum_primesBelowEnum (X + 1) fun p => archimedeanPrimeEulerCorner a (p : ℝ)
  rw [← hop]
  refine le_trans ?_ hlow
  rw [finiteReciprocalScaleL2Norm]
  apply Real.sqrt_le_sqrt
  rw [show (∑ i, (((primesBelowEnum (X + 1) i : ℕ) : ℝ))⁻¹) =
      ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ from
    sum_primesBelowEnum (X + 1) fun p => ((p : ℝ))⁻¹]
  exact log_log_sub_one_le_sum_primesBelow_inv X hX

/-- The essential norm of the all-prime Euler boundary sum grows at least like the square root
of the double logarithm of the cutoff. -/
theorem sqrt_log_log_sub_one_le_essentialNorm_sum_primesBelow_eulerCorners
    (a : ℝ) (ha : 0 < a) (X : ℕ) (hX : 1 ≤ X) :
    Real.sqrt (Real.log (Real.log ((X : ℝ) + 1)) - 1) ≤
      essentialNorm (∑ p ∈ Nat.primesBelow (X + 1), archimedeanPrimeEulerCorner a (p : ℝ)) :=
  le_essentialNorm _ _ fun K hK =>
    sqrt_log_log_sub_one_le_norm_sum_primesBelow_eulerCorners_sub_compact a ha X hX K hK

end RHTower
