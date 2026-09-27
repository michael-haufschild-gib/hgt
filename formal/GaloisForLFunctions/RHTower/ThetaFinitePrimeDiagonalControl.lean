import GaloisForLFunctions.RHTower.ThetaPrimePacketBounds
import GaloisForLFunctions.RHTower.ThetaFinitePrimeCliques
import GaloisForLFunctions.RHTower.ThetaRealTranslatedCoercivity

/-!
# Uniform diagonal reserves on arbitrarily large arithmetic packet families

A single positive diagonal constant works at every finite dimension. The
primes are chosen beyond the corresponding von Mangoldt-weight threshold;
one common radius then controls every remaining interaction. The chosen
primes and radius depend on dimension, so these spaces are not asserted to
form a nested or dense family.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem exists_cofinal_thetaFinitePrime_diagonal_control :
    ∃ C : ℝ, 0 < C ∧ ∀ N n : ℕ,
      ∃ (p : Fin n → ℕ) (r : ℝ) (hr : 0 < r),
        (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
        (∀ i j, i < j → 2 * p i < p j) ∧
        (∀ c : ℝ, C * thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0)) ≤
          thetaRealArithmeticQuadratic (thetaTranslatedBumpGround r hr c)) ∧
        (∀ i, thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
          (thetaTranslatedBumpGround r hr (Real.log (p i))) < 0 ∧
          |thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
            (thetaTranslatedBumpGround r hr (Real.log (p i)))| ≤
          (C / (2 * (n + 1 : ℝ))) *
            thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0))) ∧
        (∀ i j, i < j → 0 < thetaRealWeilPolar
          (thetaTranslatedBumpGround r hr (Real.log (p i)))
          (thetaTranslatedBumpGround r hr (Real.log (p j))) ∧
          |thetaRealWeilPolar (thetaTranslatedBumpGround r hr (Real.log (p i)))
            (thetaTranslatedBumpGround r hr (Real.log (p j)))| ≤
          (C / (2 * (n + 1 : ℝ))) *
            thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0))) := by
  classical
  obtain ⟨delta, C, hd, hC, hlocal⟩ := exists_thetaReal_center_independent_gap
  refine ⟨C, hC, fun N n => ?_⟩
  let eta : ℝ := C / (2 * (n + 1 : ℝ))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (tendsto_vonMangoldt_div_sqrt_zero.eventually
    (Iio_mem_nhds (half_pos heta)))
  let p : Fin n → ℕ := fun i => spacedPrimeSequence (max N K) i.val
  have hp (i : Fin n) : Nat.Prime (p i) := spacedPrimeSequence_prime _ _
  have hpN (i : Fin n) : N ≤ p i :=
    (le_max_left _ _).trans (spacedPrimeSequence_ge _ _)
  have hpK (i : Fin n) : K ≤ p i :=
    (le_max_right _ _).trans (spacedPrimeSequence_ge _ _)
  have hw (i : Fin n) : 2 * (ArithmeticFunction.vonMangoldt (p i) / Real.sqrt (p i)) ≤ eta := by
    have h := hK (p i) (hpK i)
    linarith only [h]
  have hpair (i j : Fin n) (hij : i < j) : 2 * p i < p j :=
    spacedPrimeSequence_double_lt _ hij
  have hhub (i : Fin n) : ∃ e : ℝ, 0 < e ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ e →
      thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (Real.log (p i))) < 0 ∧
      |thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (Real.log (p i)))| ≤
      eta * thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0)) := by
    obtain ⟨e, he, hneg⟩ := exists_thetaTranslatedBump_prime_negative_radius (hp i)
    obtain ⟨b, hb, hbound⟩ := exists_thetaTranslatedBump_prime_bound_radius (hp i)
    refine ⟨min e b, lt_min he hb, fun r hr hre => ⟨hneg r hr (hre.trans (min_le_left _ _)), ?_⟩⟩
    exact (hbound r hr (hre.trans (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_right (hw i) (thetaTranslatedBumpGround_mass_pos r hr 0).le)
  have hleaf (i j : Fin n) : ∃ e : ℝ, 0 < e ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ e →
      i < j → 0 < thetaRealWeilPolar (thetaTranslatedBumpGround r hr (Real.log (p i)))
        (thetaTranslatedBumpGround r hr (Real.log (p j))) ∧
      |thetaRealWeilPolar (thetaTranslatedBumpGround r hr (Real.log (p i)))
        (thetaTranslatedBumpGround r hr (Real.log (p j)))| ≤
      eta * thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0)) := by
    by_cases hij : i < j
    · have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
      have hlog := Real.log_lt_log (mul_pos (by positivity : (0 : ℝ) < 2) hp0)
        (show (2 : ℝ) * p i < p j by exact_mod_cast hpair i j hij)
      rw [Real.log_mul (by norm_num) hp0.ne'] at hlog
      have ht : screwSignThreshold < Real.log 2 :=
        Real.log_lt_log plasticRoot_pos plasticRoot_mem_Ioo.2
      have hgap : screwSignThreshold < Real.log (p j) - Real.log (p i) := by linarith
      have hfree (m : ℕ) (hm : 2 ≤ m) : Real.log (p j) - Real.log (p i) ≠ Real.log m :=
        prime_log_difference_ne_log_nat (hp i) (hp j) (by have := hpair i j hij; omega) hm
      obtain ⟨e, he, hpos⟩ := exists_thetaTranslatedBump_atomFree_positive_radius hgap hfree
      obtain ⟨b, hb, hbound⟩ := exists_thetaTranslatedBump_atomFree_bound_radius hgap hfree heta
      exact ⟨min e b, lt_min he hb, fun r hr hre _ =>
        ⟨hpos r hr (hre.trans (min_le_left _ _)), hbound r hr (hre.trans (min_le_right _ _))⟩⟩
    · exact ⟨1, zero_lt_one, fun _ _ _ hij' => False.elim (hij hij')⟩
  choose e he hgood using hhub
  choose b hb hleafgood using hleaf
  let eps : Unit ⊕ (Fin n ⊕ (Fin n × Fin n)) → ℝ :=
    Sum.elim (fun _ => delta / 2) (Sum.elim e (fun ij => b ij.1 ij.2))
  have heps (i : Unit ⊕ (Fin n ⊕ (Fin n × Fin n))) : 0 < eps i := by
    rcases i with i | (i | ij)
    · exact half_pos hd
    · exact he i
    · exact hb ij.1 ij.2
  obtain ⟨r, hr, hsmall⟩ := exists_pos_le_finite_family eps heps
  have hrd : r < delta := (hsmall (Sum.inl ())).trans_lt (half_lt_self hd)
  refine ⟨p, r, hr, (fun i => ⟨hpN i, hp i⟩), hpair, ?_,
    (fun i => hgood i r hr (hsmall (Sum.inr (Sum.inl i)))),
    (fun i j hij => hleafgood i j r hr (hsmall (Sum.inr (Sum.inr (i, j)))) hij)⟩
  intro c
  have hs : tsupport (thetaTranslatedBumpGround r hr c) ⊆ Metric.ball c delta :=
    (closure_minimal ((support_thetaTranslatedBumpGround r hr c).subset.trans
      Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans (Metric.closedBall_subset_ball hrd)
  have h := hlocal (thetaTranslatedBumpGround r hr c) (compact_thetaTranslatedBumpGround r hr c) c hs
  rwa [thetaTranslatedBumpGround_mass r hr c] at h

end RHTower
