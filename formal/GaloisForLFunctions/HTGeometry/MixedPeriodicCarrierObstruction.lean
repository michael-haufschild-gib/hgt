import GaloisForLFunctions.HTGeometry.FastForwardableStratumCodimension
import GaloisForLFunctions.HTGeometry.LatticeGaussianDensity

/-!
# A continuous stratum plus a lattice adds their dimensions to the codimension ceiling

If the bounded synthesis certificate holds on `W + Γ` for a subspace `W` and a full lattice `Γ`
in an orthogonal subspace `G`, then at time `t` the certificate covers a tube around the
`1/t`-rescaled copy of `W + Γ`.  Rescaling makes the lattice fine, so its neighbourhood keeps a
`t`-independent share of Gaussian mass, and only the directions orthogonal to `W ⊕ G` pay the
`t^{-1}` price.  The uniform no-shortcut exponent is therefore capped by `m − dim W − rank Γ`:
continuous synthesis dimension and discrete recurrence rank add.
-/

open MeasureTheory ProbabilityTheory Metric Set Matrix
open scoped BigOperators Matrix Matrix.Norms.L2Operator NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*} {dW r v : ℕ}

/-- Dilating the generator is the same as dilating the time. -/
theorem unitaryEvolution_smul_one (H : Matrix d d ℂ) (t : ℝ) :
    unitaryEvolution (t • H) 1 = unitaryEvolution H t := by
  rw [unitaryEvolution, unitaryEvolution, one_smul]
  congr 1
  rw [smul_comm]

theorem orbitState_eq_smul (H : Matrix d d ℂ) (ψ : EuclideanSpace ℂ d) (t : ℝ) :
    orbitState H ψ t = orbitState (t • H) ψ 1 := by
  rw [orbitState, orbitState, unitaryEvolution_smul_one]

/-- **Mixed tube inclusion.**  A coefficient vector whose `G`-part is within `δ/(2t)` of the
rescaled lattice and whose transverse part is within `δ/(2t)` of the origin inherits, at slack
`ε₊`, the bounded certificate carried by `W + Γ`. -/
theorem exists_witness_mixedTube
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ))) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    {epsMinus epsPlus delta : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin dW → ℝ) (n : Fin r → ℤ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, A (fun i => ((n i : ℤ) : ℝ)), 0)) ψ 1)
        (wordAct act w chi) ≤ epsMinus)
    (hdelta : 0 ≤ delta) (hgap : L * delta ≤ epsPlus - epsMinus)
    {t : ℝ} (ht : 0 < t) {p : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ))}
    {n : Fin r → ℤ}
    (hlat : ‖p.2.1 - t⁻¹ • A (fun i => ((n i : ℤ) : ℝ))‖ ≤ delta / (2 * t))
    (htrans : ‖p.2.2‖ ≤ delta / (2 * t)) :
    approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B := by
  classical
  set q : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ)) :=
    (t • p.1, (A (fun i => ((n i : ℤ) : ℝ)), 0)) with hq
  have hdiffvec : t • p - q = (0, (t • p.2.1 - A (fun i => ((n i : ℤ) : ℝ)), t • p.2.2)) := by
    refine Prod.ext ?_ ?_
    · simp [hq]
    · refine Prod.ext ?_ ?_ <;> simp [hq]
  have hnorm : ‖t • p - q‖ ≤ delta := by
    rw [hdiffvec]
    have h1 : ‖t • p.2.1 - A (fun i => ((n i : ℤ) : ℝ))‖ ≤ delta / 2 := by
      have hsm : t • p.2.1 - A (fun i => ((n i : ℤ) : ℝ)) =
          t • (p.2.1 - t⁻¹ • A (fun i => ((n i : ℤ) : ℝ))) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      calc t * ‖p.2.1 - t⁻¹ • A (fun i => ((n i : ℤ) : ℝ))‖
          ≤ t * (delta / (2 * t)) := mul_le_mul_of_nonneg_left hlat ht.le
        _ = delta / 2 := by field_simp
    have h2 : ‖t • p.2.2‖ ≤ delta / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      calc t * ‖p.2.2‖ ≤ t * (delta / (2 * t)) := mul_le_mul_of_nonneg_left htrans ht.le
        _ = delta / 2 := by field_simp
    simp only [Prod.norm_def, norm_zero]
    refine max_le (by positivity) ?_
    refine max_le ?_ ?_ <;> linarith
  have hmove : dist (orbitState (Hmap p) ψ t) (orbitState (Hmap q) ψ 1) ≤
      epsPlus - epsMinus := by
    have hsmul : Hmap (t • p) = t • Hmap p := map_smul Hmap t p
    have hleft : orbitState (Hmap p) ψ t = orbitState (Hmap (t • p)) ψ 1 := by
      rw [hsmul, ← orbitState_eq_smul]
    rw [hleft]
    refine le_trans (dist_orbitState_le (hherm _) (hherm q) ψ hψ 1) ?_
    have hstep : ‖Hmap (t • p) - Hmap q‖ ≤ L * delta :=
      le_trans (hlip (t • p) q) (mul_le_mul_of_nonneg_left hnorm hL.le)
    calc |(1 : ℝ)| * ‖Hmap (t • p) - Hmap q‖ = ‖Hmap (t • p) - Hmap q‖ := by simp
      _ ≤ L * delta := hstep
      _ ≤ epsPlus - epsMinus := hgap
  obtain ⟨w, hw, hd⟩ :=
    exists_witness_of_dist_le (act := act) (chi := chi) hmove (hstratum (t • p.1) n)
  refine approxComplexity_le_of_witness act chi w hw ?_
  linarith


/-- **Mixed shortcut mass.**  At time `t` the certificate covers a set of product-Gaussian measure
at least a fixed constant times `t^{-v}`, where `v` is the codimension of `W ⊕ G`. -/
theorem measure_mixedShortcut_ge
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ))) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hAinj : Function.Injective A)
    {sigma M : ℝ} (hsigpos : 0 < sigma) (hMpos : 0 < M)
    (hsig : ∀ x, sigma * ‖x‖ ≤ ‖A x‖) (hM : ∀ x, ‖A x‖ ≤ M * ‖x‖)
    {epsMinus epsPlus delta : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin dW → ℝ) (n : Fin r → ℤ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, A (fun i => ((n i : ℤ) : ℝ)), 0)) ψ 1)
        (wordAct act w chi) ≤ epsMinus)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 2) (hdeltasig : delta < sigma)
    (hgap : L * delta ≤ epsPlus - epsMinus)
    {t : ℝ} (ht1 : 1 ≤ t) (htM : M ≤ t) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * (delta / 2) / M) ^ r) *
        ENNReal.ofReal ((2 * gaussianDensityFloor * (delta / 2)) ^ v * (t ^ v)⁻¹)
      ≤ ((Measure.pi fun _ : Fin dW => gaussianReal 0 1).prod
          ((Measure.pi fun _ : Fin r => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin v => gaussianReal 0 1)))
          {p : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ)) |
            approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B} := by
  classical
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hhalf0 : (0 : ℝ) < delta / 2 := by linarith
  have hhalf1 : delta / 2 ≤ 1 := by linarith
  have h2half : 2 * (delta / 2) < sigma := by linarith
  set centers := scaledLatticeCenters A t ⌊t / M⌋₊ with hcent
  have hsub : (Set.univ ×ˢ
      ((⋃ y ∈ centers, closedBall y (delta / (2 * t))) ×ˢ
        closedBall (0 : Fin v → ℝ) (delta / (2 * t)))) ⊆
      {p : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ)) |
        approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B} := by
    rintro ⟨w, g, u⟩ ⟨-, hg, hu⟩
    obtain ⟨y, hy, hgy⟩ := Set.mem_iUnion₂.mp hg
    rw [hcent, scaledLatticeCenters, Finset.mem_image] at hy
    obtain ⟨n, -, rfl⟩ := hy
    refine exists_witness_mixedTube hψ Hmap hherm hL hlip act chi A hstratum
      hdelta0.le hgap ht0 (n := n) ?_ ?_
    · simpa [dist_eq_norm] using hgy
    · simpa [dist_eq_norm] using hu
  refine le_trans ?_ (measure_mono hsub)
  rw [Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul]
  refine mul_le_mul' ?_ ?_
  · have hlat := measure_pi_gaussian_scaledLattice_lower A hAinj hsigpos hMpos hsig hM
      hhalf0 hhalf1 h2half ht1 htM
    have hradius : delta / 2 / t = delta / (2 * t) := by field_simp
    rwa [hradius] at hlat
  · have htrans := measure_pi_gaussian_transverse_ball_lower (L := L) (ε := L * (delta / 2)) v
      hL (by positivity) ht0 (by nlinarith [hhalf1, ht1, hL])
    have hradius : L * (delta / 2) / (L * t) = delta / (2 * t) := by field_simp
    have hconst : L * (delta / 2) / L = delta / 2 := by field_simp
    rwa [hradius, hconst] at htrans

/-- **Mixed codimension ceiling.**  Continuous synthesis dimension and discrete recurrence rank
add: a uniform upper no-shortcut law `K t^{-κ}` forces `κ ≤ v = m − dim W − rank Γ`. -/
theorem exponent_le_mixedCodimension
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ))) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hAinj : Function.Injective A)
    {sigma M : ℝ} (hsigpos : 0 < sigma) (hMpos : 0 < M)
    (hsig : ∀ x, sigma * ‖x‖ ≤ ‖A x‖) (hM : ∀ x, ‖A x‖ ≤ M * ‖x‖)
    {epsMinus epsPlus delta : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin dW → ℝ) (n : Fin r → ℤ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, A (fun i => ((n i : ℤ) : ℝ)), 0)) ψ 1)
        (wordAct act w chi) ≤ epsMinus)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 2) (hdeltasig : delta < sigma)
    (hgap : L * delta ≤ epsPlus - epsMinus)
    {K kappa T : ℝ}
    (hupper : ∀ t : ℝ, T ≤ t → 1 ≤ t →
      ((Measure.pi fun _ : Fin dW => gaussianReal 0 1).prod
          ((Measure.pi fun _ : Fin r => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin v => gaussianReal 0 1))
        {p : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ)) |
          approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B}).toReal ≤
        K * t ^ (-kappa)) :
    kappa ≤ (v : ℝ) := by
  classical
  have hlatpos : 0 < (2 * gaussianFloorTwo * (delta / 2) / M) ^ r := by
    have := gaussianFloorTwo_pos
    positivity
  have htranspos : 0 < (2 * gaussianDensityFloor * (delta / 2)) ^ v := by
    have := gaussianDensityFloor_pos
    positivity
  refine exponent_le_natCast_of_forall_le
    (c := (2 * gaussianFloorTwo * (delta / 2) / M) ^ r *
      (2 * gaussianDensityFloor * (delta / 2)) ^ v)
    (K := K) (T := max T M) (by positivity) ?_
  intro t htT ht1
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have htM : M ≤ t := le_trans (le_max_right T M) htT
  have htT' : T ≤ t := le_trans (le_max_left T M) htT
  have hmeas := measure_mixedShortcut_ge hψ Hmap hherm hL hlip act chi A hAinj
    hsigpos hMpos hsig hM hstratum hdelta0 hdelta1 hdeltasig hgap ht1 htM
  have hfin : ((Measure.pi fun _ : Fin dW => gaussianReal 0 1).prod
      ((Measure.pi fun _ : Fin r => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin v => gaussianReal 0 1))
      {p : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ)) |
        approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B}) ≠ ⊤ :=
    measure_ne_top _ _
  have hstep := ENNReal.toReal_mono hfin hmeas
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlatpos.le,
    ENNReal.toReal_ofReal (by positivity)] at hstep
  have hupperT := hupper t htT' ht1
  calc (2 * gaussianFloorTwo * (delta / 2) / M) ^ r *
        (2 * gaussianDensityFloor * (delta / 2)) ^ v * (t ^ v)⁻¹
      = (2 * gaussianFloorTwo * (delta / 2) / M) ^ r *
        ((2 * gaussianDensityFloor * (delta / 2)) ^ v * (t ^ v)⁻¹) := by ring
    _ ≤ _ := hstep
    _ ≤ K * t ^ (-kappa) := hupperT


/-- **Deterministic radial mixed tube.**  At unit time the shortcut locus contains the union over
lattice points of fixed-radius tubes, so over the shell `R ≤ ‖p_W‖ ≤ 2R` its Haar measure grows
like `R^{dW} · R^{r}`: the continuous and discrete dimensions add. -/
theorem measure_mixedShortcutLocus_ge
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ))) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hAinj : Function.Injective A)
    {sigma : ℝ} (hsigpos : 0 < sigma) (hsig : ∀ x, sigma * ‖x‖ ≤ ‖A x‖)
    {epsMinus epsPlus delta : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin dW → ℝ) (n : Fin r → ℤ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, A (fun i => ((n i : ℤ) : ℝ)), 0)) ψ 1)
        (wordAct act w chi) ≤ epsMinus)
    (hdelta0 : 0 < delta) (hdeltasig : delta < sigma)
    (hgap : L * delta ≤ epsPlus - epsMinus)
    (μ : Measure (Fin dW → ℝ)) [μ.IsAddHaarMeasure]
    (ν : Measure (Fin r → ℝ)) [ν.IsAddHaarMeasure] [SFinite ν]
    (ξ : Measure (Fin v → ℝ)) [ξ.IsAddHaarMeasure] [SFinite ξ]
    {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ENNReal.ofReal ((2 ^ dW - 1) * R ^ dW) * μ (ball 0 1) *
        (((2 * N + 1) ^ r : ℕ) * (ENNReal.ofReal ((delta / 2) ^ r) * ν (ball 0 1)) *
          (ENNReal.ofReal ((delta / (2 : ℝ)) ^ v) * ξ (ball 0 1)))
      ≤ (μ.prod (ν.prod ξ))
          {p : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ)) |
            approxComplexity act chi epsPlus (orbitState (Hmap p) ψ 1) ≤ B} := by
  classical
  set centers := scaledLatticeCenters A 1 N with hcent
  have hsub : ((closedBall (0 : Fin dW → ℝ) (2 * R) \ closedBall (0 : Fin dW → ℝ) R) ×ˢ
      ((⋃ y ∈ centers, closedBall y (delta / 2)) ×ˢ
        closedBall (0 : Fin v → ℝ) (delta / 2))) ⊆
      {p : (Fin dW → ℝ) × ((Fin r → ℝ) × (Fin v → ℝ)) |
        approxComplexity act chi epsPlus (orbitState (Hmap p) ψ 1) ≤ B} := by
    rintro ⟨w, g, u⟩ ⟨-, hg, hu⟩
    obtain ⟨y, hy, hgy⟩ := Set.mem_iUnion₂.mp hg
    rw [hcent, scaledLatticeCenters, Finset.mem_image] at hy
    obtain ⟨n, -, rfl⟩ := hy
    refine exists_witness_mixedTube hψ Hmap hherm hL hlip act chi A hstratum
      hdelta0.le hgap one_pos (n := n) ?_ ?_
    · simpa [dist_eq_norm] using hgy
    · simpa [dist_eq_norm] using hu
  refine le_trans ?_ (measure_mono hsub)
  rw [Measure.prod_prod, Measure.prod_prod, measure_annulus μ hR,
    Measure.addHaar_closedBall ξ 0 (by positivity), Module.finrank_fin_fun,
    Module.finrank_fin_fun]
  refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
  have hdisj : (centers : Set (Fin r → ℝ)).PairwiseDisjoint
      fun y => closedBall y (delta / 2) := by
    intro y hy z hz hyz
    refine Metric.closedBall_disjoint_closedBall ?_
    have hsep := scaledLatticeCenters_separated A hsigpos hsig one_pos N y hy z hz hyz
    rw [div_one] at hsep
    linarith
  rw [measure_biUnion_finset hdisj (fun y _ => measurableSet_closedBall)]
  have hball : ∀ y : Fin r → ℝ, ν (closedBall y (delta / 2)) =
      ENNReal.ofReal ((delta / 2) ^ r) * ν (ball 0 1) := by
    intro y
    rw [Measure.addHaar_closedBall ν y (by positivity), Module.finrank_fin_fun]
  calc (((2 * N + 1) ^ r : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal ((delta / 2) ^ r) * ν (ball 0 1))
      = ∑ _y ∈ centers, ENNReal.ofReal ((delta / 2) ^ r) * ν (ball 0 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_scaledLatticeCenters A hAinj one_ne_zero N]
    _ = ∑ y ∈ centers, ν (closedBall y (delta / 2)) :=
        Finset.sum_congr rfl fun y _ => (hball y).symm
    _ ≤ ∑ y ∈ centers, ν (closedBall y (delta / 2)) := le_rfl

end

end GaloisForLFunctions.HTGeometry


