import GaloisForLFunctions.RHTower.XiShiftedHardEdgeBandlimitedCompactSource
import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph

/-!
# Locally uniform Route-U limit as the strong L² representative

Pointwise or locally uniform convergence of actual rational hard-edge packets is compatible with
their strong `L²` limit: an almost-everywhere convergent subsequence identifies both limits.  The
Cayley half-density tends to one, so a locally uniform squared-variable angular limit `F` gives the
physical representative `x ↦ F(x²)`.  It is automatically square-integrable, real on the physical
line, and feeds directly into the literal compact-source theorem.
-/

open MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A pointwise limit and a strong L² limit of the same representatives must coincide as an L²
class. -/
theorem toLp_eq_of_tendsto_pointwise_of_tendsto_L2
    {g : ℕ → ℝ → ℂ} (hg2 : ∀ n, MemLp (g n) 2 (volume : Measure ℝ))
    {L : Lp ℂ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun n => (hg2 n).toLp (g n)) atTop (𝓝 L))
    {f : ℝ → ℂ} (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hpoint : ∀ x : ℝ, Tendsto (fun n => g n x) atTop (𝓝 (f x))) :
    hf2.toLp f = L := by
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto hL
  have hcoe : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
      (((hg2 n).toLp (g n) : Lp ℂ 2 volume) : ℝ → ℂ) x = g n x := by
    rw [ae_all_iff]
    intro n
    exact (hg2 n).coeFn_toLp
  have hLrep : (L : ℝ → ℂ) =ᵐ[volume] f := by
    filter_upwards [hae, hcoe] with x hx hxc
    have hsub : Tendsto (fun i => g (ns i) x) atTop (𝓝 (f x)) :=
      (hpoint x).comp hns.tendsto_atTop
    have hsubL : Tendsto (fun i => g (ns i) x) atTop (𝓝 ((L : ℝ → ℂ) x)) := by
      convert hx using 1
      funext i
      exact (hxc (ns i)).symm
    exact tendsto_nhds_unique hsubL hsub
  apply Lp.ext
  exact hf2.coeFn_toLp.trans hLrep.symm

/-- Strong L² convergence plus pointwise convergence automatically proves the pointwise limit is
square-integrable and represents the strong limit. -/
theorem exists_memLp_toLp_eq_of_tendsto_pointwise_of_tendsto_L2
    {g : ℕ → ℝ → ℂ} (hg2 : ∀ n, MemLp (g n) 2 (volume : Measure ℝ))
    {L : Lp ℂ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun n => (hg2 n).toLp (g n)) atTop (𝓝 L))
    {f : ℝ → ℂ}
    (hpoint : ∀ x : ℝ, Tendsto (fun n => g n x) atTop (𝓝 (f x))) :
    ∃ hf2 : MemLp f 2 (volume : Measure ℝ), hf2.toLp f = L := by
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto hL
  have hcoe : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
      (((hg2 n).toLp (g n) : Lp ℂ 2 volume) : ℝ → ℂ) x = g n x := by
    rw [ae_all_iff]
    intro n
    exact (hg2 n).coeFn_toLp
  have hLrep : (L : ℝ → ℂ) =ᵐ[volume] f := by
    filter_upwards [hae, hcoe] with x hx hxc
    have hsub : Tendsto (fun i => g (ns i) x) atTop (𝓝 (f x)) :=
      (hpoint x).comp hns.tendsto_atTop
    have hsubL : Tendsto (fun i => g (ns i) x) atTop (𝓝 ((L : ℝ → ℂ) x)) := by
      convert hx using 1
      funext i
      exact (hxc (ns i)).symm
    exact tendsto_nhds_unique hsubL hsub
  have hf2 : MemLp f 2 (volume : Measure ℝ) :=
    (memLp_congr_ae hLrep).mp (Lp.memLp L)
  refine ⟨hf2, ?_⟩
  apply Lp.ext
  exact hf2.coeFn_toLp.trans hLrep.symm

/-- Pointwise convergence of actual rational hard-edge packets identifies a continuous candidate
with their strong L² limit; no separate representative-equality hypothesis is needed. -/
theorem routeUHardEdge_pointwise_limit_toLp_eq
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L))
    {f : ℝ → ℂ} (hf2 : MemLp f 2 volume)
    (hpoint : ∀ x : ℝ, Tendsto
      (fun k : ℕ => ((routeUHardEdgeRationalTest (a k) (p k) x : ℝ) : ℂ))
      atTop (𝓝 (f x))) :
    hf2.toLp f = ofRealLp L := by
  let g : ℕ → ℝ → ℂ := fun k x => ((routeUHardEdgeRationalTest (a k) (p k) x : ℝ) : ℂ)
  have hg2 : ∀ k, MemLp (g k) 2 (volume : Measure ℝ) := fun k =>
    memLp_ofReal (memLp_routeUHardEdgeRationalTest (ha k) (p k))
  have hLc : Tendsto (fun k => (hg2 k).toLp (g k)) atTop (𝓝 (ofRealLp L)) := by
    have hcont : Tendsto
        (fun v : Lp ℝ 2 (volume : Measure ℝ) => ofRealLp v)
        (𝓝 L) (𝓝 (ofRealLp L)) :=
      (Complex.ofRealCLM.compLpL 2 (volume : Measure ℝ)).continuous.tendsto L
    have hcomp := hcont.comp hL
    refine hcomp.congr fun k => ?_
    exact (ofRealLp_toLp (memLp_routeUHardEdgeRationalTest (ha k) (p k))).symm
  exact toLp_eq_of_tendsto_pointwise_of_tendsto_L2 hg2 hLc hf2 hpoint

theorem evalRealPolynomial_routeUHardEdgeAngularPoly_hardEdgeCoordinate
    {a : ℝ} (ha : a ≠ 0) (p : Polynomial ℝ) (x : ℝ) :
    evalRealPolynomial (routeUHardEdgeAngularPoly a p)
        ((((a ^ (2 : ℕ) - x ^ (2 : ℕ) : ℝ)) : ℂ) / (((a ^ (2 : ℕ) + x ^ (2 : ℕ) : ℝ)) : ℂ)) =
      ((p.eval ((a ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹) : ℝ) : ℂ) := by
  have hcoord :
      (((a ^ (2 : ℕ) - x ^ (2 : ℕ) : ℝ) : ℂ) / (((a ^ (2 : ℕ) + x ^ (2 : ℕ) : ℝ)) : ℂ)) =
        ((((a ^ (2 : ℕ) - x ^ (2 : ℕ)) / (a ^ (2 : ℕ) + x ^ (2 : ℕ)) : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hcoord, evalRealPolynomial_ofReal]
  simp only [routeUHardEdgeAngularPoly, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
  norm_cast
  apply congrArg (fun y : ℝ => p.eval y)
  have hden : a ^ (2 : ℕ) + x ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg x]
  field_simp [ha, hden]
  ring

theorem tendsto_routeUHardEdge_halfDensity_one
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (haT : Tendsto a atTop atTop) (x : ℝ) :
    Tendsto (fun n => a n / Real.sqrt ((a n) ^ (2 : ℕ) + x ^ (2 : ℕ))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp haT
  have hratio : Tendsto (fun n => x ^ (2 : ℕ) / (a n) ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hsq := hinv.pow 2
    have hmul := hsq.const_mul (x ^ (2 : ℕ))
    simpa [div_pow, div_eq_mul_inv] using hmul
  have hsqrt : Tendsto (fun n => Real.sqrt (1 + x ^ (2 : ℕ) / (a n) ^ (2 : ℕ))) atTop (𝓝 1) := by
    have hadd : Tendsto (fun n => 1 + x ^ (2 : ℕ) / (a n) ^ (2 : ℕ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hratio
    have hadd' : Tendsto (fun n => 1 + x ^ (2 : ℕ) / (a n) ^ (2 : ℕ)) atTop (𝓝 1) := by
      simpa only [add_zero] using hadd
    simpa only [Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto 1).comp hadd'
  have hrecip : Tendsto (fun n => (Real.sqrt (1 + x ^ (2 : ℕ) / (a n) ^ (2 : ℕ)))⁻¹)
      atTop (𝓝 1) := by
    simpa using hsqrt.inv₀ (by norm_num)
  refine hrecip.congr fun n => ?_
  have harg : 1 + x ^ (2 : ℕ) / (a n) ^ (2 : ℕ) = ((a n) ^ (2 : ℕ) + x ^ (2 : ℕ)) / (a n) ^ (2 : ℕ) := by
    field_simp [ne_of_gt (ha n)]
  rw [harg, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs,
    abs_of_pos (ha n)]
  field_simp [ne_of_gt (ha n)]

/-- A locally uniform squared-variable limit of the actual angular polynomials is the pointwise
limit of the rational hard-edge packets: the half-density tends to one. -/
theorem tendsto_routeUHardEdgeRationalTest_of_angular_locallyUniform
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ n, 0 < a n) (haT : Tendsto a atTop atTop)
    {F : ℂ → ℂ}
    (hF : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u))) F atTop)
    (x : ℝ) :
    Tendsto
      (fun n => ((routeUHardEdgeRationalTest (a n) (p n) x : ℝ) : ℂ))
      atTop (𝓝 (F ((x : ℂ) ^ (2 : ℕ)))) := by
  let u : ℂ := (x : ℂ) ^ (2 : ℕ)
  have hpoly : Tendsto
      (fun n => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u)))
      atTop (𝓝 (F u)) := by
    have huniform := (tendstoLocallyUniformly_iff_forall_isCompact.mp hF)
      ({u} : Set ℂ) isCompact_singleton
    exact huniform.tendsto_at (Set.mem_singleton u)
  have hhalf : Tendsto
      (fun n => ((a n / Real.sqrt ((a n) ^ (2 : ℕ) + x ^ (2 : ℕ)) : ℝ) : ℂ))
      atTop (𝓝 (1 : ℂ)) := by
    have hreal := tendsto_routeUHardEdge_halfDensity_one ha haT x
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto 1).comp hreal
  have heq : ∀ n,
      ((routeUHardEdgeRationalTest (a n) (p n) x : ℝ) : ℂ) =
        ((a n / Real.sqrt ((a n) ^ (2 : ℕ) + x ^ (2 : ℕ)) : ℝ) : ℂ) *
          evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
            ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u)) := by
    intro n
    have hcoord :
        ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u)) =
          ((((a n) ^ (2 : ℕ) - x ^ (2 : ℕ) : ℝ) : ℂ) /
            (((a n) ^ (2 : ℕ) + x ^ (2 : ℕ) : ℝ) : ℂ)) := by
      dsimp [u]
      push_cast
      rfl
    rw [hcoord,
      evalRealPolynomial_routeUHardEdgeAngularPoly_hardEdgeCoordinate
        (ne_of_gt (ha n))]
    simp only [routeUHardEdgeRationalTest]
    push_cast
    ring
  have hmul := hhalf.mul hpoly
  simpa [heq, u] using hmul

/-- Because every finite hard-edge packet is real on the physical line, its locally uniform
squared-variable limit is real after `u=x²`. -/
theorem routeUHardEdge_angularLocallyUniformLimit_sq_im_eq_zero
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ n, 0 < a n) (haT : Tendsto a atTop atTop)
    {F : ℂ → ℂ}
    (hF : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u))) F atTop)
    (x : ℝ) :
    (F ((x : ℂ) ^ (2 : ℕ))).im = 0 := by
  have hpoint := tendsto_routeUHardEdgeRationalTest_of_angular_locallyUniform ha haT hF x
  have him : Tendsto
      (fun n => (((routeUHardEdgeRationalTest (a n) (p n) x : ℝ) : ℂ)).im)
      atTop (𝓝 (F ((x : ℂ) ^ (2 : ℕ))).im) :=
    (Complex.continuous_im.tendsto _).comp hpoint
  have hzero : Tendsto
      (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have himzero : Tendsto
      (fun n => (((routeUHardEdgeRationalTest (a n) (p n) x : ℝ) : ℂ)).im)
      atTop (𝓝 0) := by
    simpa only [Complex.ofReal_im] using hzero
  exact tendsto_nhds_unique him himzero

/-- The locally uniform squared-variable hard-edge limit is automatically the continuous
representative of the strong L² limit and is itself square-integrable. -/
theorem exists_memLp_routeUHardEdge_angularLocallyUniformLimit_toLp_eq
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ n, 0 < a n) (haT : Tendsto a atTop atTop)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L))
    {F : ℂ → ℂ}
    (hF : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u))) F atTop) :
    ∃ hf2 : MemLp (fun x : ℝ => F ((x : ℂ) ^ (2 : ℕ))) 2 (volume : Measure ℝ),
      hf2.toLp (fun x : ℝ => F ((x : ℂ) ^ (2 : ℕ))) = ofRealLp L := by
  let g : ℕ → ℝ → ℂ := fun k x => ((routeUHardEdgeRationalTest (a k) (p k) x : ℝ) : ℂ)
  have hg2 : ∀ k, MemLp (g k) 2 (volume : Measure ℝ) := fun k =>
    memLp_ofReal (memLp_routeUHardEdgeRationalTest (ha k) (p k))
  have hLc : Tendsto (fun k => (hg2 k).toLp (g k)) atTop (𝓝 (ofRealLp L)) := by
    have hcont : Tendsto
        (fun v : Lp ℝ 2 (volume : Measure ℝ) => ofRealLp v)
        (𝓝 L) (𝓝 (ofRealLp L)) :=
      (Complex.ofRealCLM.compLpL 2 (volume : Measure ℝ)).continuous.tendsto L
    have hcomp := hcont.comp hL
    refine hcomp.congr fun k => ?_
    exact (ofRealLp_toLp (memLp_routeUHardEdgeRationalTest (ha k) (p k))).symm
  have hpoint : ∀ x : ℝ, Tendsto (fun n => g n x) atTop
      (𝓝 ((fun x : ℝ => F ((x : ℂ) ^ (2 : ℕ))) x)) := by
    intro x
    exact tendsto_routeUHardEdgeRationalTest_of_angular_locallyUniform ha haT hF x
  exact exists_memLp_toLp_eq_of_tendsto_pointwise_of_tendsto_L2 hg2 hLc hpoint

/-- The actual locally uniform hard-edge limit has a literal compact source without any separately
assumed pointwise/L² representative equality. -/
theorem routeUHardEdge_angularLocallyUniformLimit_has_literal_compact_source
    {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Tendsto a atTop atTop)
    (hb : ∀ k : ℕ, routeUHardEdgeAngularPoly (a k) (p k)
      = ∑ j ∈ Finset.range (N k + 1),
        Polynomial.C (b k j) * Polynomial.Chebyshev.T ℝ (j : ℤ))
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ (2 : ℕ)) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L))
    {F : ℂ → ℂ}
    (hFlocal : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u))) F atTop)
    (hFcont : Continuous F) :
    ∃ q : ℝ → ℂ,
      Integrable q ∧ MemLp q 2 volume ∧
      (∀ x : ℝ, x ≤ -(C / Real.pi) ∨ C / Real.pi ≤ x → q x = 0) ∧
      (∀ w : ℝ, routeURealFourier q w =
        F ((((w / (2 * Real.pi) : ℝ)) : ℂ) ^ (2 : ℕ))) := by
  obtain ⟨hf2, hrep⟩ :=
    exists_memLp_routeUHardEdge_angularLocallyUniformLimit_toLp_eq ha haT hL hFlocal
  have hfcont : Continuous (fun x : ℝ => F ((x : ℂ) ^ (2 : ℕ))) := by
    fun_prop
  exact routeUHardEdge_limit_has_literal_compact_source
    hC ha haT hb hNC hnorm hL hfcont hf2 hrep

/-- A global entire squared-root factor of the locally uniform limit transports directly to a
literal compact source with the same multiplicity. -/
theorem routeUHardEdge_angularLocallyUniformLimit_has_literal_compact_factorization
    {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Tendsto a atTop atTop)
    (hb : ∀ k : ℕ, routeUHardEdgeAngularPoly (a k) (p k)
      = ∑ j ∈ Finset.range (N k + 1),
        Polynomial.C (b k j) * Polynomial.Chebyshev.T ℝ (j : ℤ))
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ (2 : ℕ)) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L))
    {F : ℂ → ℂ}
    (hFlocal : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ (2 : ℕ)) - u) / (((a n : ℂ) ^ (2 : ℕ)) + u))) F atTop)
    (hFcont : Continuous F)
    {r : ℝ} {m : ℕ} {H : ℂ → ℂ} (hHcont : Continuous H)
    (hfactor : ∀ u : ℂ, F u = (u - (r : ℂ) ^ (2 : ℕ)) ^ m * H u) :
    ∃ q : ℝ → ℂ, ∃ G : ℝ → ℂ,
      Integrable q ∧ MemLp q 2 volume ∧ Continuous G ∧
      (∀ x : ℝ, x ≤ -(C / Real.pi) ∨ C / Real.pi ≤ x → q x = 0) ∧
      (∀ w : ℝ, routeURealFourier q w =
        (((w ^ (2 : ℕ) - (2 * Real.pi * r) ^ (2 : ℕ) : ℝ) : ℂ) ^ m) * G (w ^ (2 : ℕ))) := by
  obtain ⟨hf2, hrep⟩ :=
    exists_memLp_routeUHardEdge_angularLocallyUniformLimit_toLp_eq ha haT hL hFlocal
  have hfcont : Continuous (fun x : ℝ => F ((x : ℂ) ^ (2 : ℕ))) := by
    fun_prop
  let K : ℝ → ℂ := fun u => H (u : ℂ)
  have hK : Continuous K := by
    dsimp [K]
    fun_prop
  have hfactorReal : ∀ x : ℝ,
      F ((x : ℂ) ^ (2 : ℕ)) = (((x ^ (2 : ℕ) - r ^ (2 : ℕ) : ℝ) : ℂ) ^ m) * K (x ^ (2 : ℕ)) := by
    intro x
    rw [hfactor]
    dsimp [K]
    push_cast
    rfl
  exact routeUHardEdge_limit_has_literal_compact_factorization
    hC ha haT hb hNC hnorm hL hfcont hf2 hrep hK hfactorReal

end RHTower
