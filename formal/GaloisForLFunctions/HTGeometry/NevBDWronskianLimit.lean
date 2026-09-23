import GaloisForLFunctions.HTGeometry.NevBDWronskian
import GaloisForLFunctions.HTGeometry.DenominatorUniform
import GaloisForLFunctions.HTGeometry.KernelContinuity

/-!
# The Wronskian identity in the limit

The truncated entries converge pointwise (uniformly on bounded intervals, link to
`DenominatorUniform`) and the Christoffel--Darboux kernels converge to the bilinear kernel series, so
the finite-level identity passes to the limit:

`B(x)·D(y) − D(x)·B(y) = h₀·(x − y)·K(x,y)`.

The bilinear series converges absolutely by the arithmetic-geometric bound against the two diagonal
series, both of which are summable once the kernel is bounded.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The limiting bilinear kernel on the real axis. -/
noncomputable def kernelInf (s : ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑' k, (monicOrtho s k).eval x * (monicOrtho s k).eval y /
    momentInner s (monicOrtho s k) (monicOrtho s k)

/-- The real diagonal kernel series is summable at every point. -/
theorem summable_diag_real (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x : ℝ) :
    Summable fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  have hb : ∀ N, kernelRoot s (fun j => monicOrthoC s j ((x : ℝ) : ℂ)) N
      ≤ ballBoundQ s S P ‖((x : ℝ) : ℂ)‖ := fun N => kernelRoot_le_ballBoundQ h hS hP le_rfl N
  have hs := summable_of_kernelRoot_le h ((x : ℝ) : ℂ) hb
  have hcast : (fun k => Complex.normSq (monicOrthoC s k ((x : ℝ) : ℂ)) /
      momentInner s (monicOrtho s k) (monicOrtho s k))
      = fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
        momentInner s (monicOrtho s k) (monicOrtho s k) := by
    funext k
    rw [normSq_monicOrthoC_ofReal]
  rwa [hcast] at hs

/-- The bilinear kernel series converges absolutely. -/
theorem summable_bilinear_real (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x y : ℝ) :
    Summable fun k => (monicOrtho s k).eval x * (monicOrtho s k).eval y /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
  have hx := summable_diag_real h h0b x
  have hy := summable_diag_real h h0b y
  refine Summable.of_norm_bounded (g := fun k =>
    (((monicOrtho s k).eval x) ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k)
      + ((monicOrtho s k).eval y) ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k)) / 2)
    (((hx.add hy).div_const 2)) fun k => ?_
  have hpos : 0 < momentInner s (monicOrtho s k) (monicOrtho s k) :=
    monicOrtho_inner_self_pos h k
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by norm_num)]
  have hab : |(monicOrtho s k).eval x * (monicOrtho s k).eval y| * 2
      ≤ ((monicOrtho s k).eval x) ^ (2 : ℕ) + ((monicOrtho s k).eval y) ^ (2 : ℕ) := by
    rcases abs_cases ((monicOrtho s k).eval x * (monicOrtho s k).eval y) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> nlinarith [sq_nonneg ((monicOrtho s k).eval x - (monicOrtho s k).eval y),
        sq_nonneg ((monicOrtho s k).eval x + (monicOrtho s k).eval y)]
  have hsplit : (((monicOrtho s k).eval x) ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k)
      + ((monicOrtho s k).eval y) ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k)) / 2 * 2
      * momentInner s (monicOrtho s k) (monicOrtho s k)
      = ((monicOrtho s k).eval x) ^ (2 : ℕ) + ((monicOrtho s k).eval y) ^ (2 : ℕ) := by
    field_simp
  nlinarith [hab, hsplit, hpos]

theorem tendsto_cdKernel_eval (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x y : ℝ) :
    Tendsto (fun n => (cdKernel s n x).eval y) atTop (nhds (kernelInf s x y)) := by
  have hsum := summable_bilinear_real h h0b x y
  have hbase := hsum.hasSum.tendsto_sum_nat
  have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
  refine hshift.congr fun n => ?_
  rw [cdKernel_eval]
  rfl

theorem tendsto_nevBreal (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x : ℝ) :
    Tendsto (fun n => nevBreal s n x) atTop (nhds (nevBrealInf s x)) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hr : (0:ℝ) < |x| + 1 := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_nevBreal_close h hS hP hr hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact hN n hn x (by linarith)

theorem tendsto_nevDreal (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x : ℝ) :
    Tendsto (fun n => nevDreal s n x) atTop (nhds (nevDrealInf s x)) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hr : (0:ℝ) < |x| + 1 := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_nevDreal_close h hS hP hr hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact hN n hn x (by linarith)

/-- **The `B, D` Wronskian identity in the limit.** -/
theorem nevBD_wronskian_limit (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x y : ℝ) :
    nevBrealInf s x * nevDrealInf s y - nevDrealInf s x * nevBrealInf s y
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) * ((x - y) * kernelInf s x y) := by
  have hleft : Tendsto (fun n => nevBreal s n x * nevDreal s n y
      - nevDreal s n x * nevBreal s n y) atTop
      (nhds (nevBrealInf s x * nevDrealInf s y - nevDrealInf s x * nevBrealInf s y)) :=
    ((tendsto_nevBreal h h0b x).mul (tendsto_nevDreal h h0b y)).sub
      ((tendsto_nevDreal h h0b x).mul (tendsto_nevBreal h h0b y))
  have hright : Tendsto (fun n => momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      ((x - y) * (cdKernel s n x).eval y)) atTop
      (nhds (momentInner s (monicOrtho s 0) (monicOrtho s 0) *
        ((x - y) * kernelInf s x y))) :=
    (((tendsto_cdKernel_eval h h0b x y).const_mul (x - y)).const_mul _)
  refine tendsto_nhds_unique hleft (hright.congr fun n => ?_)
  exact (nevBD_wronskian h n x y).symm

/-- `B` and `D` have no common real zero. -/
theorem nevBrealInf_ne_zero_or_nevDrealInf_ne_zero (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (x : ℝ) :
    nevBrealInf s x ≠ 0 ∨ nevDrealInf s x ≠ 0 := by
  rcases nevBinf_ne_zero_or_nevDinf_ne_zero h h0b ((x : ℝ) : ℂ) with hB | hD
  · left
    intro hc
    exact hB (by rw [nevBinf_ofReal, hc, Complex.ofReal_zero])
  · right
    intro hc
    exact hD (by rw [nevDinf_ofReal, hc, Complex.ofReal_zero])

/-- **At a point of the fiber, `B` cannot vanish.**  Both entries vanishing is forbidden by the
determinant identity. -/
theorem nevBrealInf_ne_zero_of_mem_fiber (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {t ξ : ℝ} (hξ : nevBrealInf s ξ * t - nevDrealInf s ξ = 0) : nevBrealInf s ξ ≠ 0 := by
  intro hB
  rcases nevBrealInf_ne_zero_or_nevDrealInf_ne_zero h h0b ξ with hc | hD
  · exact hc hB
  · refine hD ?_
    rw [hB, zero_mul, zero_sub, neg_eq_zero] at hξ
    exact hξ

/-- **The denominator factors through the kernel at a fiber point.**  This exhibits `B·t − D` near
`ξ` as `(x − ξ)` times a continuous nonvanishing factor, hence a sign change. -/
theorem nevDenominator_factor_at_fiber (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {t ξ : ℝ} (hξ : nevBrealInf s ξ * t - nevDrealInf s ξ = 0) (x : ℝ) :
    (nevBrealInf s x * t - nevDrealInf s x) * nevBrealInf s ξ
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) * ((x - ξ) * kernelInf s x ξ) := by
  have hD : nevDrealInf s ξ = nevBrealInf s ξ * t := by linarith
  rw [← nevBD_wronskian_limit h h0b x ξ, hD]
  ring

end HTGeometry
