import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryDeterminant

/-!
# Route P primitive Gamma--Julia ordinary determinant cofinal uniformity

P-G105N proved pointwise convergence of literal finite physical determinants to the reflected
ordinary determinant. Divisor passage needs local uniformity, not pointwise convergence.

The missing topological step is subtle: the available uniform-product theorem assumes a group and
therefore does not apply to complex multiplication at zero. We prove the exact normed-ring
replacement needed here: two uniformly convergent complex families have uniformly convergent
products on a nonempty set when both limit functions are norm-bounded there.

On every closed disc, the coordinate is bounded, the trace is constant, and both limiting
exponential and det2 factors are bounded by compactness. Hence finite literal ordinary determinants
converge uniformly on every closed disc and locally uniformly on the whole complex plane.

This closes P-G105O. Aperture-wall convergence and Xi-divisor identification remain.
-/

open Complex Matrix Filter Topology Set
open ContinuousLinearMap
open scoped Kronecker ComplexOrder BigOperators InnerProductSpace Matrix

namespace RHTower

noncomputable section

/-- Uniform multiplication for complex-valued families on a nonempty set, under boundedness of
the two limiting functions. Unlike the uniform-group theorem, this permits zeros. -/
theorem tendstoUniformlyOn_mul_complex_of_bddAbove
    {ι α : Type*} {p : Filter ι} {K : Set α}
    {f f' : ι → α → ℂ} {g g' : α → ℂ}
    (hf : TendstoUniformlyOn f g p K)
    (hf' : TendstoUniformlyOn f' g' p K)
    (hK : K.Nonempty)
    (hg : BddAbove ((fun x => ‖g x‖) '' K))
    (hg' : BddAbove ((fun x => ‖g' x‖) '' K)) :
    TendstoUniformlyOn (fun i x => f i x * f' i x)
      (fun x => g x * g' x) p K := by
  obtain ⟨C, hC⟩ := hg
  obtain ⟨D, hD⟩ := hg'
  obtain ⟨x0, hx0⟩ := hK
  have hC0 : 0 ≤ C :=
    (norm_nonneg (g x0)).trans (hC (mem_image_of_mem (fun x => ‖g x‖) hx0))
  let B : ℝ := max C D + 1
  have hBpos : 0 < B := by
    dsimp [B]
    linarith [le_max_left C D]
  have hgB : ∀ x ∈ K, ‖g x‖ < B := by
    intro x hx
    have hxC := hC (mem_image_of_mem (fun y => ‖g y‖) hx)
    dsimp [B]
    linarith [le_max_left C D]
  have hg'B : ∀ x ∈ K, ‖g' x‖ < B := by
    intro x hx
    have hxD := hD (mem_image_of_mem (fun y => ‖g' y‖) hx)
    dsimp [B]
    linarith [le_max_right C D]
  rw [Metric.tendstoUniformlyOn_iff] at hf hf' ⊢
  intro eps heps
  let delta : ℝ := min 1 (eps / (2 * B))
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min one_pos (div_pos heps (mul_pos (by norm_num) hBpos))
  have hdelta_one : delta ≤ 1 := min_le_left _ _
  have hdelta_eps : delta ≤ eps / (2 * B) := min_le_right _ _
  filter_upwards [hf delta hdelta_pos, hf' delta hdelta_pos] with i hi hi'
  intro x hx
  have hdiff : ‖g x - f i x‖ < delta := by
    simpa [dist_eq_norm] using hi x hx
  have hdiff' : ‖g' x - f' i x‖ < delta := by
    simpa [dist_eq_norm] using hi' x hx
  have hfiB : ‖f i x‖ < B := by
    have hdist : dist (f i x) (g x) < delta := by
      rw [dist_comm]
      exact hi x hx
    have hnorm := norm_le_norm_add_const_of_dist_le (le_refl (dist (f i x) (g x)))
    have hxC := hC (mem_image_of_mem (fun y => ‖g y‖) hx)
    have hxM : ‖g x‖ ≤ max C D := hxC.trans (le_max_left C D)
    dsimp [B]
    linarith
  rw [dist_eq_norm]
  calc
    ‖g x * g' x - f i x * f' i x‖ =
        ‖(g x - f i x) * g' x + f i x * (g' x - f' i x)‖ := by
          congr 1
          ring
    _ ≤ ‖g x - f i x‖ * ‖g' x‖ + ‖f i x‖ * ‖g' x - f' i x‖ := by
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    _ < delta * B + B * delta := by
      exact add_lt_add
        (calc
          ‖g x - f i x‖ * ‖g' x‖ ≤ delta * ‖g' x‖ :=
            mul_le_mul_of_nonneg_right hdiff.le (norm_nonneg _)
          _ < delta * B := mul_lt_mul_of_pos_left (hg'B x hx) hdelta_pos)
        (calc
          ‖f i x‖ * ‖g' x - f' i x‖ ≤ B * ‖g' x - f' i x‖ :=
            mul_le_mul_of_nonneg_right hfiB.le (norm_nonneg _)
          _ < B * delta := mul_lt_mul_of_pos_left hdiff' hBpos)
    _ = 2 * B * delta := by ring
    _ ≤ 2 * B * (eps / (2 * B)) := by
      exact mul_le_mul_of_nonneg_left hdelta_eps (mul_nonneg (by norm_num) hBpos.le)
    _ = eps := by
      field_simp [ne_of_gt hBpos]

/-- Literal finite physical ordinary determinants converge uniformly on every positive-radius
closed disc. -/
theorem tendstoUniformlyOn_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) {rho : ℝ} (hrho : 0 < rho) :
    TendstoUniformlyOn
      (fun s z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r)
      atTop (Metric.closedBall 0 rho) := by
  let a : ℂ := ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r))
  have htrace : Tendsto
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r) atTop
      (nhds a) :=
    tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace hd hr
  have hconst : TendstoUniformlyOn
      (fun s : Finset (Fin 2 × Nat.Primes) => fun _ : ℂ =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s)
      (fun _ : ℂ => a) atTop (Metric.closedBall 0 rho) :=
    htrace.tendstoUniformlyOn_const _
  have hid : TendstoUniformlyOn
      (fun _ : Finset (Fin 2 × Nat.Primes) => fun z : ℂ => z)
      (fun z : ℂ => z) atTop (Metric.closedBall 0 rho) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    filter_upwards [] with s
    intro z hz
    simpa using heps
  have hmul : TendstoUniformlyOn
      (fun s : Finset (Fin 2 × Nat.Primes) => fun z : ℂ =>
        z * routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s)
      (fun z : ℂ => z * a) atTop (Metric.closedBall 0 rho) := by
    apply tendstoUniformlyOn_mul_complex_of_bddAbove hid hconst
    · exact ⟨0, by simp [Metric.mem_closedBall, hrho.le]⟩
    · refine ⟨rho, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    · refine ⟨‖a‖, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact le_rfl
  have hbdd : BddAbove
      ((fun z : ℂ => (z * a).re) '' Metric.closedBall 0 rho) := by
    refine ⟨rho * ‖a‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hnorm : ‖z‖ ≤ rho := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    calc
      (z * a).re ≤ ‖z * a‖ := Complex.re_le_norm _
      _ = ‖z‖ * ‖a‖ := norm_mul z a
      _ ≤ rho * ‖a‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg a)
  have hexp0 := hmul.comp_cexp hbdd
  have hexp : TendstoUniformlyOn
      (fun s : Finset (Fin 2 × Nat.Primes) => fun z : ℂ =>
        Complex.exp
          (z * routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s))
      (fun z : ℂ => Complex.exp (z * a)) atTop (Metric.closedBall 0 rho) := by
    simpa [Function.comp_def] using hexp0
  have hop : a = ((1 - r : ℝ) : ℂ) *
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) := by
    exact opTrace_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator hd hr
  have hexp' : TendstoUniformlyOn
      (fun s : Finset (Fin 2 × Nat.Primes) => fun z : ℂ =>
        Complex.exp
          (z * routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s))
      (fun z : ℂ => Complex.exp (z * (((1 - r : ℝ) : ℂ) *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))))
      atTop (Metric.closedBall 0 rho) := by
    simpa [hop] using hexp
  have hdet0 :=
    tendstoUniformlyOn_routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteDet2
      hd r hrho
  have hdetComp := hdet0.comp (fun z : ℂ => -z)
  have hdet : TendstoUniformlyOn
      (fun s : Finset (Fin 2 × Nat.Primes) => fun z : ℂ =>
        GaloisForLFunctions.HTGeometry.finiteDet2
          (-(HilbertSchmidt.blockMatrix
            (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s)) (-z))
      (fun z : ℂ =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r (-z))
      atTop (Metric.closedBall 0 rho) := by
    simpa [Function.comp_def, Metric.mem_closedBall, dist_zero_right] using hdetComp
  have hexpBdd : BddAbove
      ((fun z : ℂ => ‖Complex.exp (z * (((1 - r : ℝ) : ℂ) *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)))‖) ''
        Metric.closedBall 0 rho) :=
    (isCompact_closedBall (0 : ℂ) rho).bddAbove_image
      ((Complex.continuous_exp.comp
        (continuous_id.mul continuous_const)).norm.continuousOn)
  have hdetBdd : BddAbove
      ((fun z : ℂ => ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r (-z)‖) ''
        Metric.closedBall 0 rho) :=
    (isCompact_closedBall (0 : ℂ) rho).bddAbove_image
      ((((differentiable_routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 hd r).comp
        differentiable_neg).continuous).norm.continuousOn)
  have hprod := tendstoUniformlyOn_mul_complex_of_bddAbove
    hexp' hdet (by exact ⟨0, by simp [Metric.mem_closedBall, hrho.le]⟩)
      hexpBdd hdetBdd
  change TendstoUniformlyOn
    (fun s z => Complex.exp
      (z * routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s) *
      GaloisForLFunctions.HTGeometry.finiteDet2
        (-(HilbertSchmidt.blockMatrix
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s)) (-z))
    (fun z => Complex.exp (z * (((1 - r : ℝ) : ℂ) *
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))) *
      routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r (-z))
    atTop (Metric.closedBall 0 rho)
  exact hprod

/-- Literal finite physical ordinary determinants converge locally uniformly on the complex plane. -/
theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    TendstoLocallyUniformly
      (fun s z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r)
      atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let rho : ℝ := |R| + 1
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  apply (tendstoUniformlyOn_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet
    hd hr hrho).mono
  exact hKR.trans (Metric.closedBall_subset_closedBall (by
    dsimp [rho]
    linarith [le_abs_self R]))

/-- **P-G105O capstone.** Cofinal literal finite ordinary determinants converge uniformly on every
closed disc and locally uniformly on the whole complex plane. -/
theorem routePPrimitive_GammaJulia_physicalStokesHellingerOrdinaryDeterminantCofinalUniform
    (d : ℝ) (hd : 0 < d) (r : ℝ) (hr : 0 ≤ r) :
    (∀ rho : ℝ, 0 < rho → TendstoUniformlyOn
      (fun s z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r)
      atTop (Metric.closedBall 0 rho)) ∧
    TendstoLocallyUniformly
      (fun s z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r)
      atTop :=
  ⟨fun _ hrho =>
      tendstoUniformlyOn_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet
        hd hr hrho,
    tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet
      hd hr⟩

end

end RHTower
