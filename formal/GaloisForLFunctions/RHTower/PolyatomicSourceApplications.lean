import GaloisForLFunctions.HTGeometry.PolyatomicSpectralRank
import GaloisForLFunctions.HTGeometry.PolyatomicBeta
import GaloisForLFunctions.HTGeometry.PolyatomicConservation
import GaloisForLFunctions.RHTower.MobiusGammaHankelMultiplierCollapse
import GaloisForLFunctions.RHTower.ReflectedBiHeatSourceFaithfulMarkovNormalizationNoGo

/-!
# Polyatomic factorization in the existing Gamma--Hankel and two-channel sources

The collision-energy Laplace feature is exactly the corpus's Gamma--Hankel
atom at a square-root integer energy node. This transfers finite independence
and nonsingularity to the literal completed source atoms. Separately, the
beta-derived Landau--Teller rate selects an explicit member of the existing
conservative two-channel Markov family. These are exact identifications;
they assert no new arithmetic estimate or RH implication.
-/

open MeasureTheory Set Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The existing integer-frequency Gamma atom is an actual collision-energy feature. -/
theorem gammaLaplaceAtom_eq_collisionLaplaceAtom (a : ℝ) (n : ℕ) :
    gammaLaplaceAtom ⟨Real.exp a, Real.exp_pos a⟩ n =
      collisionLaplaceAtom a 0 (Real.sqrt ((n : ℝ) + 1 / 2)) := by
  apply Lp.ext
  filter_upwards [gammaLaplaceAtom_ae ⟨Real.exp a, Real.exp_pos a⟩ n,
    collisionLaplaceAtom_ae a 0 (Real.sqrt ((n : ℝ) + 1 / 2))] with t hg hc
  rw [hg, hc]
  have hs : Real.sqrt ((n : ℝ) + 1 / 2) ^ 2 = (n : ℝ) + 1 / 2 :=
    Real.sq_sqrt (by positivity)
  simp only [gammaLaplaceFeature, collisionLaplaceFeature, Real.exp_zero, hs]
  congr 3
  push_cast
  ring

/-- Every finite set of the actual consecutive Gamma--Hankel atoms is independent. -/
theorem gammaLaplaceAtom_linearIndependent_fin (a : ℝ) (N : ℕ) :
    LinearIndependent ℂ
      (fun n : Fin N => gammaLaplaceAtom ⟨Real.exp a, Real.exp_pos a⟩ n) := by
  simp_rw [gammaLaplaceAtom_eq_collisionLaplaceAtom]
  apply (collisionLaplaceAtom_linearIndependent_iff a 0 _).mpr
  intro i j h
  simp only [Real.sq_sqrt (show 0 ≤ (i : ℝ) + 1 / 2 by positivity),
    Real.sq_sqrt (show 0 ≤ (j : ℝ) + 1 / 2 by positivity)] at h
  have hv : (i : ℝ) = (j : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast hv)

/-- The completed source Gamma--Hankel Gram has no finite-dimensional kernel. -/
theorem gammaLaplaceAtom_gram_det_ne_zero (a : ℝ) (N : ℕ) :
    (Matrix.gram ℂ
      (fun n : Fin N => gammaLaplaceAtom ⟨Real.exp a, Real.exp_pos a⟩ n)).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (gammaLaplaceAtom_linearIndependent_fin a N)

/-- The corpus's conservative Markov flow is the equal-weight collision-mode relaxation. -/
theorem reflectedBiHeatMarkovFlow_eq_collisionRelaxation (r t : ℝ) (p : ℝ × ℝ) :
    reflectedBiHeatMarkovFlow (r ^ 2 / 2) t p = collisionRelaxation 1 r t p := by
  have he : Real.exp (-2 * (r ^ 2 / 2) * t) = Real.exp (-r ^ 2 * t) := by
    congr 1
    ring
  apply Prod.ext <;>
    simp only [reflectedBiHeatMarkovFlow, collisionRelaxation,
      collisionConservationProject, collisionExchange, Prod.fst_add,
      Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, he] <;> ring

/-- An explicit thermal exchange flow with the rate derived from the kinetic beta partition. -/
def polyatomicLandauTellerFlow (d t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  reflectedBiHeatMarkovFlow (polyatomicLandauTellerRate d / 2) t p

/-- Identification with the exact orthogonal invariant/exchange decomposition. -/
theorem polyatomicLandauTellerFlow_eq_collisionRelaxation (d t : ℝ) (p : ℝ × ℝ) :
    polyatomicLandauTellerFlow d t p =
      collisionRelaxation 1 (Real.sqrt (polyatomicLandauTellerRate d)) t p := by
  have hr : 0 ≤ polyatomicLandauTellerRate d :=
    le_of_lt (lt_trans (by norm_num) (polyatomicLandauTeller_rate_bounds d).1)
  rw [← reflectedBiHeatMarkovFlow_eq_collisionRelaxation, Real.sq_sqrt hr]
  rfl

/-- The two energy pools conserve their sum under the beta-selected flow. -/
theorem polyatomicLandauTellerFlow_conservation (d t : ℝ) (p : ℝ × ℝ) :
    (polyatomicLandauTellerFlow d t p).1 + (polyatomicLandauTellerFlow d t p).2 =
      p.1 + p.2 :=
  reflectedBiHeatMarkovFlow_add _ _ _

/-- The temperature difference obeys the analytically derived exponential rate. -/
theorem polyatomicLandauTellerFlow_exchange (d t : ℝ) (p : ℝ × ℝ) :
    (polyatomicLandauTellerFlow d t p).1 - (polyatomicLandauTellerFlow d t p).2 =
      Real.exp (-polyatomicLandauTellerRate d * t) * (p.1 - p.2) := by
  rw [polyatomicLandauTellerFlow, reflectedBiHeatMarkovFlow_sub]
  congr 2
  ring

/-- Every finite-time thermal map retains the complete incoming pair. -/
theorem polyatomicLandauTellerFlow_injective (d t : ℝ) :
    Function.Injective (polyatomicLandauTellerFlow d t) :=
  reflectedBiHeatMarkovFlow_injective _ _

/-- Thermal relaxation never creates exact balance at finite time. -/
theorem polyatomicLandauTellerFlow_balance_iff (d t : ℝ) (p : ℝ × ℝ) :
    (polyatomicLandauTellerFlow d t p).1 = (polyatomicLandauTellerFlow d t p).2 ↔
      p.1 = p.2 :=
  reflectedBiHeatMarkovFlow_balance_iff _ _ _

/-- Nevertheless every initial temperature difference decays to zero at infinite time. -/
theorem polyatomicLandauTellerFlow_exchange_tendsto (d : ℝ) (p : ℝ × ℝ) :
    Tendsto (fun t : ℝ => (polyatomicLandauTellerFlow d t p).1 -
      (polyatomicLandauTellerFlow d t p).2) atTop (𝓝 0) := by
  apply reflectedBiHeatMarkovFlow_sub_tendsto
  have h := (polyatomicLandauTeller_rate_bounds d).1
  linarith

end RHTower
