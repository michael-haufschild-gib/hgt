import GaloisForLFunctions.HTGeometry.CaratheodoryFejerStrictAtomicFactorization
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Semidefinite Carathéodory--Fejér atomic factorization

This module closes the reverse finite realization step for a normalized
positive-semidefinite Toeplitz section.  Diagonal perturbations make the data
strictly positive definite; their Bernstein--Szegő probability laws have a
cluster point on the compact circle probability space.  Weak continuity of
the finite Fourier window identifies the limit with the original PSD data, and
finite circle cubature gives an exact unit-circle atomic Gram factorization.

No representing measure for the PSD input is assumed.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal Topology ComplexOrder

noncomputable section

/-- Diagonal perturbation of a two-sided circle-moment sequence. -/
def toeplitzDiagonalPerturb (c : ℤ → ℂ) (ε : ℝ) (q : ℤ) : ℂ :=
  c q + if q = 0 then (ε : ℂ) else 0

/-- The diagonal moment perturbation is literally scalar identity addition on
every finite Toeplitz section. -/
theorem circleToeplitzGram_toeplitzDiagonalPerturb (N : ℕ) (c : ℤ → ℂ) (ε : ℝ) :
    circleToeplitzGram N (toeplitzDiagonalPerturb c ε) =
      circleToeplitzGram N c + ε • 1 := by
  ext i j
  simp only [circleToeplitzGram, toeplitzDiagonalPerturb, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp
  · have hq : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ≠ 0 := by
      intro hz
      have hijZ : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := sub_eq_zero.mp hz
      have hijN : (i : ℕ) = (j : ℕ) := by exact_mod_cast hijZ
      exact h (Fin.ext hijN)
    simp [hq, h]

/-- Adding a positive diagonal perturbation to PSD Toeplitz data makes it
positive definite. -/
theorem circleToeplitzGram_toeplitzDiagonalPerturb_posDef
    {N : ℕ} {c : ℤ → ℂ} {ε : ℝ}
    (hG : (circleToeplitzGram N c).PosSemidef) (hε : 0 < ε) :
    (circleToeplitzGram N (toeplitzDiagonalPerturb c ε)).PosDef := by
  rw [circleToeplitzGram_toeplitzDiagonalPerturb]
  exact Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.smul Matrix.PosDef.one hε)

/-- Mass-normalized diagonal perturbation. -/
def toeplitzNormalizedDiagonalPerturb (c : ℤ → ℂ) (ε : ℝ) (q : ℤ) : ℂ :=
  ((1 + ε : ℝ)⁻¹ : ℂ) * toeplitzDiagonalPerturb c ε q

/-- Positive perturbations decreasing to zero. -/
noncomputable def toeplitzPerturbationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem toeplitzPerturbationScale_pos (n : ℕ) : 0 < toeplitzPerturbationScale n := by
  simp [toeplitzPerturbationScale]
  positivity

theorem toeplitzPerturbationScale_tendsto :
    Tendsto toeplitzPerturbationScale atTop (nhds 0) := by
  unfold toeplitzPerturbationScale
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Each normalized perturbation converges coefficientwise to the original
circle-moment sequence. -/
theorem toeplitzNormalizedDiagonalPerturb_tendsto (c : ℤ → ℂ) (q : ℤ) :
    Tendsto (fun n : ℕ =>
      toeplitzNormalizedDiagonalPerturb c (toeplitzPerturbationScale n) q)
      atTop (nhds (c q)) := by
  have hε : Tendsto (fun n : ℕ => (toeplitzPerturbationScale n : ℂ))
      atTop (nhds 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp toeplitzPerturbationScale_tendsto
  have hden : Tendsto (fun n : ℕ => (1 + (toeplitzPerturbationScale n : ℝ) : ℂ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hε
  have hfactor : Tendsto (fun n : ℕ =>
      ((1 + toeplitzPerturbationScale n : ℝ)⁻¹ : ℂ)) atTop (nhds 1) := by
    convert hden.inv₀ (by norm_num : (1 : ℂ) ≠ 0) using 1 <;> simp
  by_cases hq : q = 0
  · subst q
    have hnum : Tendsto (fun n : ℕ =>
        c 0 + (toeplitzPerturbationScale n : ℂ)) atTop (nhds (c 0)) := by
      simpa using (tendsto_const_nhds (x := c 0)).add hε
    simpa [toeplitzNormalizedDiagonalPerturb, toeplitzDiagonalPerturb] using hfactor.mul hnum
  · have hnum : Tendsto (fun _ : ℕ => c q) atTop (nhds (c q)) := tendsto_const_nhds
    simpa [toeplitzNormalizedDiagonalPerturb, toeplitzDiagonalPerturb, hq] using
      hfactor.mul hnum

theorem toeplitzNormalizedDiagonalPerturb_zero (c : ℤ → ℂ) {ε : ℝ}
    (hc0 : c 0 = 1) (hε : 0 < ε) :
    toeplitzNormalizedDiagonalPerturb c ε 0 = 1 := by
  simp only [toeplitzNormalizedDiagonalPerturb, toeplitzDiagonalPerturb, hc0, if_pos]
  convert inv_mul_cancel₀ (show ((1 + ε : ℝ) : ℂ) ≠ 0 by
    norm_cast
    linarith) using 1
  all_goals norm_cast

theorem toeplitzNormalizedDiagonalPerturb_isHermitian
    (c : ℤ → ℂ) (ε : ℝ) (hc : IsHermitianMoment c) :
    IsHermitianMoment (toeplitzNormalizedDiagonalPerturb c ε) := by
  intro r
  let s : ℂ := ((1 + ε : ℝ)⁻¹ : ℂ)
  have hs : star s = s := by simp [s]
  change s * (c (-(r : ℤ)) + if -(r : ℤ) = 0 then (ε : ℂ) else 0) =
    star (s * (c (r : ℤ) + if (r : ℤ) = 0 then (ε : ℂ) else 0))
  rw [star_mul, hs]
  rw [mul_comm]
  apply congrArg (fun z : ℂ => z * s)
  rw [star_add]
  rw [hc r]
  by_cases hr : (r : ℤ) = 0
  · simp [hr]
  · have hrNat : r ≠ 0 := by
      intro hzero
      apply hr
      simp [hzero]
    simp [hrNat]

/-- Normalized positive diagonal perturbation preserves positive definiteness. -/
theorem circleToeplitzGram_toeplitzNormalizedDiagonalPerturb_posDef
    {N : ℕ} {c : ℤ → ℂ} {ε : ℝ}
    (hG : (circleToeplitzGram N c).PosSemidef) (hε : 0 < ε) :
    (circleToeplitzGram N (toeplitzNormalizedDiagonalPerturb c ε)).PosDef := by
  have hscale : (0 : ℝ) < (1 + ε)⁻¹ := by positivity
  have hpert := circleToeplitzGram_toeplitzDiagonalPerturb_posDef hG hε
  rw [show circleToeplitzGram N (toeplitzNormalizedDiagonalPerturb c ε) =
      (1 + ε : ℝ)⁻¹ • circleToeplitzGram N (toeplitzDiagonalPerturb c ε) by
    ext i j
    simp [circleToeplitzGram, toeplitzNormalizedDiagonalPerturb, Matrix.smul_apply,
      Algebra.smul_def]]
  exact Matrix.PosDef.smul hpert hscale

/-- A normalized PSD Toeplitz section has a genuine circle probability
realization.  The one-step larger PSD section supplies the strict perturbation
needed for the Bernstein--Szegő realization. -/
theorem exists_probabilityMeasure_circleToeplitzGram_eq_of_posSemidef
    {N : ℕ} (c : ℤ → ℂ) (hc0 : c 0 = 1)
    (hG : (circleToeplitzGram (N + 1) c).PosSemidef) :
    ∃ μ : ProbabilityMeasure Circle,
      circleToeplitzGram N (circleMeasureMomentZ (μ : Measure Circle)) =
        circleToeplitzGram N c := by
  let ε : ℕ → ℝ := toeplitzPerturbationScale
  have hεpos : ∀ n : ℕ, 0 < ε n := toeplitzPerturbationScale_pos
  have hPD : ∀ n : ℕ,
      (circleToeplitzGram (N + 1) (toeplitzNormalizedDiagonalPerturb c (ε n))).PosDef :=
    fun n => circleToeplitzGram_toeplitzNormalizedDiagonalPerturb_posDef hG (hεpos n)
  let μs : ℕ → ProbabilityMeasure Circle := fun n =>
    ⟨bernsteinSzegoMeasure (toeplitzNormalizedDiagonalPerturb c (ε n)) (hPD n),
      IsProbabilityMeasure.mk (bernsteinSzegoMeasure_univ _ (hPD n)
        (toeplitzNormalizedDiagonalPerturb_zero c hc0 (hεpos n)))⟩
  obtain ⟨μ, -, hcl⟩ :=
    (isCompact_univ (X := ProbabilityMeasure Circle)).exists_clusterPt
      (f := map μs atTop) (by simp)
  have hmoment : ∀ (n : ℕ) (q : ℤ), q.natAbs ≤ N + 1 →
      circleMeasureMomentZ (μs n : Measure Circle) q =
        toeplitzNormalizedDiagonalPerturb c (ε n) q := by
    intro n q hq
    change circleMeasureMomentZ
      (bernsteinSzegoMeasure (toeplitzNormalizedDiagonalPerturb c (ε n)) (hPD n)) q = _
    rw [circleMeasureMomentZ_bernsteinSzegoMeasure]
    cases q with
    | ofNat k =>
        have hk : k ≤ N + 1 := by simpa using hq
        exact (bernsteinSzegoMoment_prefix _ (hPD n) ⟨k, by omega⟩).1
    | negSucc k =>
        have hk : k + 1 ≤ N + 1 := by simpa only [Int.natAbs_negSucc] using hq
        rw [Int.negSucc_eq]
        convert (bernsteinSzegoMoment_prefix _ (hPD n) ⟨k + 1, by omega⟩).2 using 1 <;>
          push_cast <;> ring
  have hclusterMoment : ∀ q : ℤ, q.natAbs ≤ N + 1 →
      circleMeasureMomentZ (μ : Measure Circle) q = c q := by
    intro q hq
    let g : ProbabilityMeasure Circle → ℂ :=
      fun ν => circleMeasureMomentZ (ν : Measure Circle) q
    have hgc : Continuous g := by
      simpa only [g] using continuous_circleMeasureMomentZ q
    have hval : ∀ n : ℕ, g (μs n) =
        toeplitzNormalizedDiagonalPerturb c (ε n) q := by
      intro n
      exact hmoment n q hq
    have hlim : Tendsto (fun n : ℕ => g (μs n)) atTop (nhds (c q)) := by
      exact (toeplitzNormalizedDiagonalPerturb_tendsto c q).congr
        (fun n => (hval n).symm)
    have hmaple : map (fun n : ℕ => g (μs n)) atTop ≤ nhds (c q) := hlim
    have hclg : (nhds (g μ) ⊓ map (fun n : ℕ => g (μs n)) atTop).NeBot := by
      haveI : (nhds μ ⊓ map μs atTop).NeBot := hcl
      have hmono : map g (nhds μ ⊓ map μs atTop) ≤
          nhds (g μ) ⊓ map (fun n : ℕ => g (μs n)) atTop := by
        refine le_inf (le_trans (map_mono inf_le_left) hgc.continuousAt) ?_
        calc
          map g (nhds μ ⊓ map μs atTop) ≤ map g (map μs atTop) := map_mono inf_le_right
          _ = map (fun n : ℕ => g (μs n)) atTop := by
            rw [Filter.map_map]
            rfl
      exact Filter.NeBot.mono
        (Filter.map_neBot (m := g) (f := nhds μ ⊓ map μs atTop)) hmono
    have hne : (nhds (g μ) ⊓ nhds (c q)).NeBot :=
      hclg.mono (inf_le_inf_left _ hmaple)
    exact eq_of_nhds_neBot hne
  refine ⟨μ, ?_⟩
  apply circleToeplitzGram_eq_of_moment_eq
  intro q hqleft hqright
  apply hclusterMoment q
  have : q.natAbs ≤ N := by omega
  omega

/-- A normalized PSD Toeplitz section has a genuine circle probability
realization at the same truncation depth.  For positive depth this is the
diagonal-perturbation/compactness argument; depth zero is the unit Dirac law.

This is the finite truncated-Herglotz direction.  In particular, it does not
assume either a representing measure or a one-step PSD extension of the input
section. -/
theorem exists_probabilityMeasure_circleToeplitzGram_eq_of_posSemidef_same
    {N : ℕ} (c : ℤ → ℂ) (hc0 : c 0 = 1)
    (hG : (circleToeplitzGram N c).PosSemidef) :
    ∃ μ : ProbabilityMeasure Circle,
      circleToeplitzGram N (circleMeasureMomentZ (μ : Measure Circle)) =
        circleToeplitzGram N c := by
  cases N with
  | zero =>
      let μ : ProbabilityMeasure Circle := ⟨Measure.dirac (1 : Circle), inferInstance⟩
      refine ⟨μ, ?_⟩
      ext i j
      fin_cases i
      fin_cases j
      simp [circleToeplitzGram, circleMeasureMomentZ_zero, hc0]
  | succ N =>
      let ε : ℕ → ℝ := toeplitzPerturbationScale
      have hεpos : ∀ n : ℕ, 0 < ε n := toeplitzPerturbationScale_pos
      have hPD : ∀ n : ℕ,
          (circleToeplitzGram (N + 1)
            (toeplitzNormalizedDiagonalPerturb c (ε n))).PosDef :=
        fun n => circleToeplitzGram_toeplitzNormalizedDiagonalPerturb_posDef hG (hεpos n)
      let μs : ℕ → ProbabilityMeasure Circle := fun n =>
        ⟨bernsteinSzegoMeasure (toeplitzNormalizedDiagonalPerturb c (ε n)) (hPD n),
          IsProbabilityMeasure.mk (bernsteinSzegoMeasure_univ _ (hPD n)
            (toeplitzNormalizedDiagonalPerturb_zero c hc0 (hεpos n)))⟩
      obtain ⟨μ, -, hcl⟩ :=
        (isCompact_univ (X := ProbabilityMeasure Circle)).exists_clusterPt
          (f := map μs atTop) (by simp)
      have hmoment : ∀ (n : ℕ) (q : ℤ), q.natAbs ≤ N + 1 →
          circleMeasureMomentZ (μs n : Measure Circle) q =
            toeplitzNormalizedDiagonalPerturb c (ε n) q := by
        intro n q hq
        change circleMeasureMomentZ
          (bernsteinSzegoMeasure (toeplitzNormalizedDiagonalPerturb c (ε n)) (hPD n)) q = _
        rw [circleMeasureMomentZ_bernsteinSzegoMeasure]
        cases q with
        | ofNat k =>
            have hk : k ≤ N + 1 := by simpa using hq
            exact (bernsteinSzegoMoment_prefix _ (hPD n) ⟨k, by omega⟩).1
        | negSucc k =>
            have hk : k + 1 ≤ N + 1 := by simpa only [Int.natAbs_negSucc] using hq
            rw [Int.negSucc_eq]
            convert (bernsteinSzegoMoment_prefix _ (hPD n) ⟨k + 1, by omega⟩).2 using 1 <;>
              push_cast <;> ring
      have hclusterMoment : ∀ q : ℤ, q.natAbs ≤ N + 1 →
          circleMeasureMomentZ (μ : Measure Circle) q = c q := by
        intro q hq
        let g : ProbabilityMeasure Circle → ℂ :=
          fun ν => circleMeasureMomentZ (ν : Measure Circle) q
        have hgc : Continuous g := by
          simpa only [g] using continuous_circleMeasureMomentZ q
        have hval : ∀ n : ℕ, g (μs n) =
            toeplitzNormalizedDiagonalPerturb c (ε n) q := by
          intro n
          exact hmoment n q hq
        have hlim : Tendsto (fun n : ℕ => g (μs n)) atTop (nhds (c q)) := by
          exact (toeplitzNormalizedDiagonalPerturb_tendsto c q).congr
            (fun n => (hval n).symm)
        have hmaple : map (fun n : ℕ => g (μs n)) atTop ≤ nhds (c q) := hlim
        have hclg : (nhds (g μ) ⊓ map (fun n : ℕ => g (μs n)) atTop).NeBot := by
          haveI : (nhds μ ⊓ map μs atTop).NeBot := hcl
          have hmono : map g (nhds μ ⊓ map μs atTop) ≤
              nhds (g μ) ⊓ map (fun n : ℕ => g (μs n)) atTop := by
            refine le_inf (le_trans (map_mono inf_le_left) hgc.continuousAt) ?_
            calc
              map g (nhds μ ⊓ map μs atTop) ≤ map g (map μs atTop) := map_mono inf_le_right
              _ = map (fun n : ℕ => g (μs n)) atTop := by
                rw [Filter.map_map]
                rfl
          exact Filter.NeBot.mono
            (Filter.map_neBot (m := g) (f := nhds μ ⊓ map μs atTop)) hmono
        have hne : (nhds (g μ) ⊓ nhds (c q)).NeBot :=
          hclg.mono (inf_le_inf_left _ hmaple)
        exact eq_of_nhds_neBot hne
      refine ⟨μ, ?_⟩
      apply circleToeplitzGram_eq_of_moment_eq
      intro q hqleft hqright
      apply hclusterMoment q
      omega

/-- **Semidefinite Carathéodory--Fejér factorization.** Every normalized
Hermitian PSD Toeplitz section is exactly a nonnegative unit-circle atomic
Vandermonde Gram matrix. -/
theorem exists_atomic_caratheodoryFejer_psd_factorization
    {N : ℕ} (c : ℤ → ℂ) (hc : IsHermitianMoment c) (hc0 : c 0 = 1)
    (hG : (circleToeplitzGram N c).PosSemidef) :
    ∃ (weight : Fin ((N + N) + 1) → ℝ)
      (node : Fin ((N + N) + 1) → ℂ),
      (∀ i, 0 ≤ weight i) ∧ (∀ i, ‖node i‖ = 1) ∧
        circleToeplitzGram N c = caratheodoryFejerAtomicGram (n := N) node weight := by
  obtain ⟨μ, hμ⟩ :=
    exists_probabilityMeasure_circleToeplitzGram_eq_of_posSemidef_same c hc0 hG
  obtain ⟨weight, atom, hweight, hsum, hprefix⟩ :=
    exists_atomic_circleFourier_prefix μ N
  refine ⟨weight, fun i => (atom i : ℂ), hweight,
    fun i => Circle.norm_coe (atom i), ?_⟩
  have hatomic : IsHermitianMoment (circleAtomicMoment (fun i => (atom i : ℂ)) weight) :=
    circleAtomicMoment_isHermitian _ _ (fun i => Circle.norm_coe (atom i))
  have hpositive : ∀ r ≤ N,
      c (r : ℤ) = circleAtomicMoment (fun i => (atom i : ℂ)) weight (r : ℤ) := by
    intro r hr
    cases r with
    | zero =>
        change c 0 = circleAtomicMoment (fun i => (atom i : ℂ)) weight 0
        rw [hc0]
        unfold circleAtomicMoment
        calc
          (1 : ℂ) = ∑ i, (weight i : ℂ) := by
            calc
              (1 : ℂ) = Complex.ofRealHom 1 := rfl
              _ = Complex.ofRealHom (∑ i, weight i) := congrArg _ hsum.symm
              _ = ∑ i, Complex.ofRealHom (weight i) :=
                map_sum Complex.ofRealHom (fun i => weight i) Finset.univ
          _ = ∑ i, (weight i : ℂ) * (atom i : ℂ) ^ (-(0 : ℤ)) := by simp
    | succ r =>
        let k : Fin N := ⟨r, by omega⟩
        have hsource : circleMeasureMomentZ (μ : Measure Circle) ((r + 1 : ℕ) : ℤ) =
            c ((r + 1 : ℕ) : ℤ) :=
          positiveMoment_eq_of_circleToeplitzGram_eq hμ (r + 1) (by omega)
        calc
          c ((r + 1 : ℕ) : ℤ) =
              circleMeasureMomentZ (μ : Measure Circle) ((r + 1 : ℕ) : ℤ) := hsource.symm
          _ = ∑ i, (weight i : ℂ) * (atom i : ℂ) ^ (-((r + 1 : ℕ) : ℤ)) := by
              convert hprefix k using 1
              simp [k]
          _ = circleAtomicMoment (fun i => (atom i : ℂ)) weight ((r + 1 : ℕ) : ℤ) := by
              rfl
  calc
    circleToeplitzGram N c =
        circleToeplitzGram N (circleAtomicMoment (fun i => (atom i : ℂ)) weight) :=
      (circleToeplitzGram_eq_iff_positiveMoment_eq hc hatomic).2 hpositive
    _ = caratheodoryFejerAtomicGram (n := N) (fun i => (atom i : ℂ)) weight :=
      (caratheodoryFejerAtomicGram_eq_circleAtomicToeplitz _ _ hweight
        (fun i => Circle.norm_coe (atom i))).symm

end

end GaloisForLFunctions.HTGeometry
