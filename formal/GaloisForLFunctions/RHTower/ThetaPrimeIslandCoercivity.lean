import GaloisForLFunctions.RHTower.ThetaPrimeIslandPairBounds
import GaloisForLFunctions.RHTower.ThetaFinitePrimeCliques
import GaloisForLFunctions.RHTower.ThetaFiniteSourceQuadratic
import GaloisForLFunctions.RHTower.FiniteSourceMassBudget

/-!
# Coercivity on arbitrary profiles in finitely many prime islands

One positive constant works for every finite number of support regions. Each
region admits every compact real Schwartz profile, with arbitrary oscillation
and mass. The selected primes and common radius depend on the number of regions.
The complete prime-power interaction is included throughout.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem exists_cofinal_thetaReal_primeIsland_coercivity :
    ∃ k : ℝ, 0 < k ∧ ∀ N n : ℕ,
      ∃ (p : Fin n → ℕ) (r : ℝ), 0 < r ∧
        (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
        (∀ i j, i < j → 2 * p i < p j) ∧
        ∀ phi : Option (Fin n) → 𝓢(ℝ, ℝ),
          (∀ i, HasCompactSupport (phi i)) →
          (∀ i, tsupport (phi i) ⊆ Metric.ball (i.elim 0 (fun j => Real.log (p j))) r) →
          k * (∑ i, thetaGroundNormSq (thetaComplexify (phi i))) ≤
            thetaRealArithmeticQuadratic (∑ i, phi i) := by
  classical
  obtain ⟨delta, C, hd, hC, hlocal⟩ := exists_thetaReal_center_independent_gap
  refine ⟨C / 2, half_pos hC, fun N n => ?_⟩
  let eta : ℝ := C / (4 * (n + 1 : ℝ))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (tendsto_vonMangoldt_div_sqrt_zero.eventually
    (Iio_mem_nhds heta))
  let p : Fin n → ℕ := fun i => spacedPrimeSequence (max N K) i.val
  have hp (i : Fin n) : Nat.Prime (p i) := spacedPrimeSequence_prime _ _
  have hpN (i : Fin n) : N ≤ p i :=
    (le_max_left _ _).trans (spacedPrimeSequence_ge _ _)
  have hpK (i : Fin n) : K ≤ p i :=
    (le_max_right _ _).trans (spacedPrimeSequence_ge _ _)
  have hw (i : Fin n) : ArithmeticFunction.vonMangoldt (p i) / Real.sqrt (p i) ≤ eta :=
    (hK (p i) (hpK i)).le
  have hpair (i j : Fin n) (hij : i < j) : 2 * p i < p j :=
    spacedPrimeSequence_double_lt _ hij
  have hhub (i : Fin n) := exists_thetaPrime_island_pair_bound (hp i)
  have hleaf (i j : Fin n) : ∃ e : ℝ, 0 < e ∧ ∀ r : ℝ, 0 < r → r ≤ e →
      i < j → ∀ phi psi : 𝓢(ℝ, ℝ), HasCompactSupport phi → HasCompactSupport psi →
      tsupport phi ⊆ Metric.ball (Real.log (p i)) r →
      tsupport psi ⊆ Metric.ball (Real.log (p j)) r →
      |thetaRealWeilPolar phi psi| ≤ eta *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
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
      obtain ⟨e, he, hbound⟩ := exists_thetaAtomFree_island_pair_bound hgap hfree heta
      exact ⟨e, he, fun r hr hre _ phi psi hc hd hs ht =>
        hbound r hr hre phi psi hc hd (subset_closure.trans hs) (subset_closure.trans ht)⟩
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
  have hrd : r ≤ delta := (hsmall (Sum.inl ())).trans (half_le_self hd.le)
  refine ⟨p, r, hr, (fun i => ⟨hpN i, hp i⟩), hpair, fun phi hc hs => ?_⟩
  let m := fun i => thetaGroundNormSq (thetaComplexify (phi i))
  have hm (i) : 0 ≤ m i := thetaGroundNormSq_nonneg _
  have hdiag (i) : C * m i ≤ thetaRealWeilPolar (phi i) (phi i) := by
    rw [thetaRealWeilPolar_compact_self _ (hc i)]
    exact hlocal (phi i) (hc i) _ ((hs i).trans (Metric.ball_subset_ball hrd))
  have hh (i : Fin n) : |thetaRealWeilPolar (phi none) (phi (some i))| ≤
      eta * (m none + m (some i)) := by
    exact (hgood i r hr (hsmall (Sum.inr (Sum.inl i))) _ _
      (hc none) (hc (some i)) (subset_closure.trans (hs none))
        (subset_closure.trans (hs (some i)))).trans
        (mul_le_mul_of_nonneg_right (hw i) (add_nonneg (hm none) (hm (some i))))
  have hl (i j : Fin n) (hij : i < j) :
      |thetaRealWeilPolar (phi (some i)) (phi (some j))| ≤
        eta * (m (some i) + m (some j)) :=
    hleafgood i j r hr (hsmall (Sum.inr (Sum.inr (i, j)))) hij _ _
      (hc (some i)) (hc (some j)) (hs (some i)) (hs (some j))
  have hoff (i j : Option (Fin n)) (hij : i ≠ j) :
      |thetaRealWeilPolar (phi i) (phi j)| ≤ eta * (m i + m j) := by
    rcases i with _ | i <;> rcases j with _ | j
    · exact False.elim (hij rfl)
    · exact hh j
    · rw [thetaRealWeilPolar_compact_symm _ _ (hc _) (hc _), add_comm]
      exact hh i
    · rcases lt_or_gt_of_ne (show i ≠ j from fun h => hij (congrArg some h)) with h | h
      · exact hl i j h
      · rw [thetaRealWeilPolar_compact_symm _ _ (hc _) (hc _), add_comm]
        exact hl j i h
  have h := finiteSignedQuadratic_mass_gap
    (fun i j => thetaRealWeilPolar (phi i) (phi j)) m C eta hm heta.le hdiag hoff
  have hcoef : C - 2 * (Fintype.card (Option (Fin n)) : ℝ) * eta = C / 2 := by
    simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp only [eta]
    field_simp
    ring
  rw [hcoef] at h
  simpa only [finiteSignedQuadratic, mul_one, ← thetaRealArithmeticQuadratic_finite_sum phi hc]
    using h

end RHTower
