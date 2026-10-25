import GaloisForLFunctions.RHTower.Deninger.DeningerTriangularShift
import GaloisForLFunctions.ArithmeticOrientationTheory.InteriorWienerJets
import GaloisForLFunctions.ArithmeticOrientationTheory.VisiblePolesImposeIndependentPaidConditions

/-!
# Finite Wiener jets can be prescribed

Pairwise separating factors give masks supported at one finite jet target.
Powers of a dyadic simple local parameter then give invertible triangular
jet matrices, proving simultaneous interpolation in the Wiener algebra.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

/-- Subtracting its value makes the dyadic point mass a simple local zero. -/
def wienerLocalParameter (s : ℂ) : WienerAlgebraAt (1 / 2) :=
  pointMass 2 - algebraMap ℂ (WienerAlgebraAt (1 / 2)) ((2 : ℂ) ^ (-s))

theorem wienerLocalParameter_order {s : ℂ} (hs : 1 / 2 < s.re) :
    analyticOrderAt (LSeries (⇑(wienerLocalParameter s).toFn)) s = 1 := by
  have heq : LSeries (⇑(wienerLocalParameter s).toFn) =ᶠ[𝓝 s]
      (fun z : ℂ => (2 : ℂ) ^ (-z) - (2 : ℂ) ^ (-s)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    rw [wienerLocalParameter, wienerLSeries_sub_algebraMap _ _ hz.le,
      wienerLSeries_pointMass two_ne_zero]
    norm_num only [Nat.cast_ofNat]
  have hA := analyticAt_wienerLSeries (wienerLocalParameter s) hs
  apply hA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · rw [heq.eq_of_nhds, sub_self]
  · have hd : HasDerivAt (fun z : ℂ => (2 : ℂ) ^ (-z) - (2 : ℂ) ^ (-s))
        ((2 : ℂ) ^ (-s) * Complex.log 2 * (-1)) s := by
      simpa only [Pi.neg_apply, id_eq] using ((hasDerivAt_id s).neg.const_cpow
        (Or.inl (two_ne_zero : (2 : ℂ) ≠ 0))).sub_const ((2 : ℂ) ^ (-s))
    rw [heq.deriv_eq, hd.deriv]
    have hp : (2 : ℂ) ^ (-s) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      simp
    have hl : Complex.log (2 : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos one_lt_two).ne'
    exact mul_ne_zero (mul_ne_zero hp hl) (neg_ne_zero.mpr one_ne_zero)

/-- A zero value contributes at least one analytic order. -/
theorem one_le_wiener_order_of_zero (a : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : 1 / 2 < s.re) (ha : LSeries (⇑a.toFn) s = 0) :
    (1 : ℕ∞) ≤ analyticOrderAt (LSeries (⇑a.toFn)) s := by
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 1)
    (analyticAt_wienerLSeries a hs)).mpr
  intro k hk
  have hk0 : k = 0 := by omega
  simpa only [hk0, iteratedDeriv_zero] using ha

/-- Finite interior jets can be prescribed jointly in the critical Wiener algebra. -/
theorem exists_wiener_with_prescribed_finite_jets
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) (hinj : Function.Injective s)
    (m : ι → ℕ) (v : ι → ℕ → ℂ) :
    ∃ a : WienerAlgebraAt (1 / 2), ∀ i k, k < m i →
      iteratedDeriv k (LSeries (⇑a.toFn)) (s i) = v i k := by
  classical
  let χ (i : ι) := WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) (s i) (hs i).le)
  have hsep (i j : ι) (hij : i ≠ j) : ∃ a : WienerAlgebraAt (1 / 2), χ i a ≠ χ j a :=
    halfPlane_characters_separated (hs i).le (hs j).le (fun h => hij (hinj h))
  choose a ha using hsep
  -- Each mask vanishes to the prescribed orders away from its own target.
  let b (i j : ι) : WienerAlgebraAt (1 / 2) := if h : j = i then 1 else
    a i j (Ne.symm h) - algebraMap ℂ (WienerAlgebraAt (1 / 2)) (χ j (a i j (Ne.symm h)))
  let mask (i : ι) : WienerAlgebraAt (1 / 2) := ∏ j, b i j ^ m j
  let Q (i : ι) (k : ℕ) : WienerAlgebraAt (1 / 2) := mask i * wienerLocalParameter (s i) ^ k
  have hbself (i j : ι) : χ i (b i j) ≠ 0 := by
    dsimp only [b]
    split_ifs with h
    · rw [map_one]
      exact one_ne_zero
    · rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply]
      exact sub_ne_zero.mpr (ha i j (Ne.symm h))
  have hbother (i j : ι) (hji : j ≠ i) : χ j (b i j) = 0 := by
    dsimp only [b]
    rw [dif_neg hji, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hmask (i : ι) : LSeries (⇑(mask i).toFn) (s i) ≠ 0 := by
    rw [wienerLSeries_eq_character _ (hs i).le]
    change χ i (∏ j, b i j ^ m j) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by
      rw [map_pow]
      exact pow_ne_zero _ (hbself i j)
  have hself (i : ι) (k : ℕ) :
      analyticOrderAt (LSeries (⇑(Q i k).toFn)) (s i) = (k : ℕ∞) := by
    dsimp only [Q]
    rw [analyticOrderAt_wiener_mul _ _ (hs i),
      (analyticAt_wienerLSeries (mask i) (hs i)).analyticOrderAt_eq_zero.mpr (hmask i),
      zero_add, analyticOrderAt_wiener_pow _ (hs i), wienerLocalParameter_order (hs i)]
    simp
  have hother (i j : ι) (hji : j ≠ i) (k : ℕ) :
      (m j : ℕ∞) ≤ analyticOrderAt (LSeries (⇑(Q i k).toFn)) (s j) := by
    have hdiv : b i j ^ m j ∣ mask i := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    obtain ⟨r, hr⟩ := hdiv
    have hz : LSeries (⇑(b i j).toFn) (s j) = 0 := by
      rw [wienerLSeries_eq_character _ (hs j).le]
      exact hbother i j hji
    have h1 := one_le_wiener_order_of_zero (b i j) (hs j) hz
    have hn : (m j : ℕ∞) ≤ (m j) • analyticOrderAt (LSeries (⇑(b i j).toFn)) (s j) := by
      calc
        (m j : ℕ∞) = (m j) • (1 : ℕ∞) := by simp
        _ ≤ _ := by gcongr
    dsimp only [Q]
    rw [hr, analyticOrderAt_wiener_mul _ _ (hs j),
      analyticOrderAt_wiener_mul _ _ (hs j), analyticOrderAt_wiener_pow _ (hs j)]
    exact hn.trans (le_self_add.trans le_self_add)
  let J (i : ι) (k : ℕ) := wienerJetLinear (s i) (hs i) k
  let M (i : ι) (k l : ℕ) : ℂ := J i k (Q i l)
  have hzero (i : ι) (k l : ℕ) (hkl : k < l) : M i k l = 0 := by
    exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (analyticAt_wienerLSeries (Q i l) (hs i))).mp (hself i l)).1 k hkl
  have hdiag (i : ι) (k : ℕ) : M i k k ≠ 0 := by
    exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (analyticAt_wienerLSeries (Q i k) (hs i))).mp (hself i k)).2
  -- Exact local orders give a triangular jet matrix with nonzero diagonal.
  have hsolve (i : ι) : ∃ c : ℕ → ℂ, ∀ k < m i,
      ∑ l ∈ Finset.range (m i), c l * M i k l = v i k :=
    RHTower.deningerTriangular_solvable (M i) (hzero i) (hdiag i) (v i) (m i)
  choose c hc using hsolve
  refine ⟨∑ i, ∑ l ∈ Finset.range (m i), c i l • Q i l, fun i k hk => ?_⟩
  change J i k (∑ j, ∑ l ∈ Finset.range (m j), c j l • Q j l) = v i k
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · exact hc i k hk
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro l _
    have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_wienerLSeries (Q j l) (hs i))).mp (hother j i hji.symm l) k hk
    change c j l * iteratedDeriv k (LSeries (⇑(Q j l).toFn)) (s i) = 0
    rw [hz, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

/-- Joint finite jet evaluation is onto, with all target multiplicities retained. -/
theorem surjective_wiener_finite_jet_evaluation
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) (hinj : Function.Injective s) (m : ι → ℕ) :
    Function.Surjective (fun a : WienerAlgebraAt (1 / 2) =>
      fun i (k : Fin (m i)) => wienerJetLinear (s i) (hs i) k a) := by
  classical
  intro v
  obtain ⟨a, ha⟩ := exists_wiener_with_prescribed_finite_jets s hs hinj m
    (fun i k => if h : k < m i then v i ⟨k, h⟩ else 0)
  refine ⟨a, funext fun i => funext fun k => ?_⟩
  exact (ha i k k.isLt).trans (dif_pos k.isLt)

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.wienerLocalParameter_order
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_wiener_with_prescribed_finite_jets
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.surjective_wiener_finite_jet_evaluation
end
