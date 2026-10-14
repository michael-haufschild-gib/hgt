import GaloisForLFunctions.RHTower.TwistedArcGenerator

/-!
# The twisted point generator is the spherical bi-Laplacian of the Poisson root

For `x ∈ ℝ` and an arc parameter `c` put `Q_c(x) = x² − 2cx + 1` and `s(c) = Q_c(x)^{−1/2}`, the
Poisson root of the unit-circle point with real part `c`, viewed as a function of `c`.  On the unit
circle `c = cos α`, and the spherical Laplacian `(sin α)^{−1} ∂_α sin α ∂_α` is the Legendre
operator `ℒ = ∂_c (1 − c²) ∂_c` (`legendreOp`).

**Theorem** (`twPointVec_eq_legendreOp_sq`).  If `Q_c(x) > 0`, then

`τ_c(x) = ℒ²[s](c)`,

where `τ_c = twPointVec c` is the twisted point generator
`4c x Q^{−3/2} + (42c² − 18) x² Q^{−5/2} + 120c(c² − 1) x³ Q^{−7/2} + 105(1 − c²)² x⁴ Q^{−9/2}`.

Proof.  `s' = x s³`, so every derivative of a polynomial in `(c, s)` is again one; with
`Q^{−k−1/2} = s^{2k+1}`:
`ℒ s = 3(1 − c²) x² s⁵ − 2c x s³`,
`(ℒ s)' = −12c x² s⁵ + 15(1 − c²) x³ s⁷ − 2x s³`,
`(ℒ s)'' = −18 x² s⁵ − 90c x³ s⁷ + 105(1 − c²) x⁴ s⁹`,
and `(1 − c²)(ℒ s)'' − 2c (ℒ s)'` is the generator, term by term.

The dilation operator `𝒟 = −∂_x x² ∂_x` acts on `Q_c(x)^{−1/2}` in `x` exactly as `ℒ` acts in `c`
(`𝒟 = ℒ` on the Poisson root), so the twisted generator `g_u = √y 𝒟² ψ_u` equals `√y ℒ² ψ_u` with
the derivatives taken in the arc parameter.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The Legendre operator `ℒ f = (1 − c²) f'' − 2c f'`: the spherical Laplacian in `c = cos α`. -/
def legendreOp (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  (1 - c ^ 2) * deriv (deriv f) c - 2 * c * deriv f c

/-- The Poisson root `s(c) = Q_c(x)^{−1/2}` as a function of the arc parameter. -/
def poissonRoot (x c : ℝ) : ℝ := arcQuad c x ^ (-1 / 2 : ℝ)

theorem isOpen_arcQuad_pos (x : ℝ) : IsOpen {c : ℝ | 0 < arcQuad c x} :=
  isOpen_lt continuous_const (by unfold arcQuad; fun_prop)

theorem poissonRoot_pos {x c : ℝ} (hQ : 0 < arcQuad c x) : 0 < poissonRoot x c :=
  Real.rpow_pos_of_pos hQ _

/-- `Q^{−1/2 − k} = s^{2k+1}`, i.e. `arcQuadTerm c k x = s(c)^{2k+1}`. -/
theorem arcQuadTerm_eq_poissonRoot_pow {x c : ℝ} (hQ : 0 < arcQuad c x) (k : ℕ) :
    arcQuadTerm c k x = poissonRoot x c ^ (2 * k + 1) := by
  unfold arcQuadTerm poissonRoot
  have hs : (arcQuad c x ^ (-1 / 2 : ℝ)) ^ 2 = (arcQuad c x)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    norm_num
    exact Real.rpow_neg_one _
  rw [pow_succ, pow_mul, hs, inv_pow, div_eq_mul_inv, mul_comm]

/-- `s' = x s³`. -/
theorem hasDerivAt_poissonRoot {x c : ℝ} (hQ : 0 < arcQuad c x) :
    HasDerivAt (poissonRoot x) (x * poissonRoot x c ^ 3) c := by
  have hQd : HasDerivAt (fun c => arcQuad c x) (-2 * x) c := by
    have h := (((hasDerivAt_id c).const_mul (2 * x)).const_sub (x ^ 2)).add_const 1
    have e : (fun c => arcQuad c x) = fun y => x ^ 2 - 2 * x * id y + 1 := by
      funext y; unfold arcQuad; simp only [id]; ring
    rw [e]
    exact h.congr_deriv (by ring)
  have h := hQd.rpow_const (p := (-1 / 2 : ℝ)) (Or.inl hQ.ne')
  have e : arcQuad c x ^ ((-1 / 2 : ℝ) - 1) = (arcQuad c x ^ (-1 / 2 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    norm_num
  unfold poissonRoot
  refine h.congr_deriv ?_
  rw [e]
  ring

/-- `(s^k)' = k x s^{k+2}`. -/
theorem hasDerivAt_poissonRoot_pow {x c : ℝ} (hQ : 0 < arcQuad c x) (k : ℕ) :
    HasDerivAt (fun c => poissonRoot x c ^ k) (k * x * poissonRoot x c ^ (k + 2)) c := by
  have h : HasDerivAt (fun c => poissonRoot x c ^ k)
      (k * poissonRoot x c ^ (k - 1) * (x * poissonRoot x c ^ 3)) c :=
    (hasDerivAt_poissonRoot hQ).pow k
  refine h.congr_deriv ?_
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- `deriv f` agrees with `g` near `c` when `f` has derivative `g` on the open set `Q > 0`. -/
theorem deriv_eventuallyEq_of_arcQuad_pos {x c : ℝ} (hQ : 0 < arcQuad c x) {f g : ℝ → ℝ}
    (hf : ∀ c', 0 < arcQuad c' x → HasDerivAt f (g c') c') : deriv f =ᶠ[𝓝 c] g :=
  Filter.eventually_of_mem ((isOpen_arcQuad_pos x).mem_nhds hQ) fun c' hc' => (hf c' hc').deriv

/-- **The twisted point generator is `ℒ²` of the Poisson root.** -/
theorem twPointVec_eq_legendreOp_sq {x c : ℝ} (hQ : 0 < arcQuad c x) :
    twPointVec c x = legendreOp (legendreOp (poissonRoot x)) c := by
  set s := poissonRoot x with hs
  have d1 : ∀ c', 0 < arcQuad c' x → HasDerivAt s (x * s c' ^ 3) c' := fun c' h =>
    hasDerivAt_poissonRoot h
  have d2 : ∀ c', 0 < arcQuad c' x →
      HasDerivAt (fun c => x * s c ^ 3) (3 * x ^ 2 * s c' ^ 5) c' := fun c' h =>
    ((hasDerivAt_poissonRoot_pow h 3).const_mul x).congr_deriv (by push_cast; ring)
  set F : ℝ → ℝ := fun c => 3 * (1 - c ^ 2) * x ^ 2 * s c ^ 5 - 2 * c * x * s c ^ 3 with hF
  have hLs : ∀ c', 0 < arcQuad c' x → legendreOp s c' = F c' := fun c' h => by
    unfold legendreOp
    rw [(deriv_eventuallyEq_of_arcQuad_pos h d1).deriv_eq, (d2 c' h).deriv, (d1 c' h).deriv]
    simp only [hF]
    ring
  have hLsev : legendreOp s =ᶠ[𝓝 c] F :=
    Filter.eventually_of_mem ((isOpen_arcQuad_pos x).mem_nhds hQ) fun c' hc' => hLs c' hc'
  set F1 : ℝ → ℝ := fun c =>
    -12 * c * x ^ 2 * s c ^ 5 + 15 * (1 - c ^ 2) * x ^ 3 * s c ^ 7 - 2 * x * s c ^ 3 with hF1
  set F2 : ℝ → ℝ := fun c =>
    -18 * x ^ 2 * s c ^ 5 - 90 * c * x ^ 3 * s c ^ 7 + 105 * (1 - c ^ 2) * x ^ 4 * s c ^ 9 with hF2
  have e1 : ∀ c', 0 < arcQuad c' x → HasDerivAt F (F1 c') c' := fun c' h => by
    have h5 := hasDerivAt_poissonRoot_pow h 5
    have h3 := hasDerivAt_poissonRoot_pow h 3
    have hp : HasDerivAt (fun c : ℝ => 3 * (1 - c ^ 2) * x ^ 2) (3 * (-(2 * c')) * x ^ 2) c' :=
      ((((hasDerivAt_pow 2 c').const_sub 1).const_mul 3).mul_const (x ^ 2)).congr_deriv
        (by push_cast; ring)
    have hq : HasDerivAt (fun c : ℝ => 2 * c * x) (2 * x) c' :=
      (((hasDerivAt_id c').const_mul 2).mul_const x).congr_deriv (by simp)
    exact ((hp.mul h5).sub (hq.mul h3)).congr_deriv (by simp only [hF1]; push_cast; ring)
  have e2 : ∀ c', 0 < arcQuad c' x → HasDerivAt F1 (F2 c') c' := fun c' h => by
    have h5 := hasDerivAt_poissonRoot_pow h 5
    have h7 := hasDerivAt_poissonRoot_pow h 7
    have h3 := hasDerivAt_poissonRoot_pow h 3
    have ha : HasDerivAt (fun c : ℝ => -12 * c * x ^ 2) (-12 * x ^ 2) c' :=
      (((hasDerivAt_id c').const_mul (-12)).mul_const (x ^ 2)).congr_deriv (by simp)
    have hb : HasDerivAt (fun c : ℝ => 15 * (1 - c ^ 2) * x ^ 3) (15 * (-(2 * c')) * x ^ 3) c' :=
      ((((hasDerivAt_pow 2 c').const_sub 1).const_mul 15).mul_const (x ^ 3)).congr_deriv
        (by push_cast; ring)
    exact (((ha.mul h5).add (hb.mul h7)).sub (h3.const_mul (2 * x))).congr_deriv
      (by simp only [hF2]; push_cast; ring)
  have hd1 : deriv (legendreOp s) =ᶠ[𝓝 c] F1 :=
    hLsev.deriv.trans (deriv_eventuallyEq_of_arcQuad_pos hQ e1)
  show twPointVec c x =
    (1 - c ^ 2) * deriv (deriv (legendreOp s)) c - 2 * c * deriv (legendreOp s) c
  rw [hLsev.deriv_eq, hd1.deriv_eq, (e2 c hQ).deriv, (e1 c hQ).deriv]
  unfold twPointVec
  rw [arcQuadTerm_eq_poissonRoot_pow hQ, arcQuadTerm_eq_poissonRoot_pow hQ,
    arcQuadTerm_eq_poissonRoot_pow hQ, arcQuadTerm_eq_poissonRoot_pow hQ]
  simp only [hF1, hF2]
  ring

end

end RHTower
