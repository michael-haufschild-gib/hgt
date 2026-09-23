import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# Two-point positivity of the squared-Xi Euler response

An off-critical Xi quartet has a signed Krein decomposition, but its squared-zero response atom
lies in a much smaller chamber than a generic indefinite packet.  The critical strip and the
source-derived height gap force its radial response to decrease strictly while its radius-weighted
response increases strictly.  These two inequalities are exactly the two factors of every
two-point Euler-kernel determinant.

Consequently every nonempty finite packet of actual Xi squared-zero orbits has positive diagonal
and strictly positive two-point determinant, without RH.  This is the finite, dependency-closed
core of the paper theorem that any negative infinitesimal Euler-ray detector must use at least
three nodes.
-/

open Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Abstract squared-orbit response -/

/-- The real radial response of one conjugate pair of squared zeros. -/
def squaredEulerOrbitResponse (t c u : ℝ) : ℝ :=
  (t + u) / ((t + u) ^ (2 : ℕ) + c)

/-- The chamber in which the squared-zero pair lies strictly to the left of its radial aperture. -/
def SquaredEulerOrbitChamber (t c : ℝ) : Prop :=
  0 < t ∧ 0 ≤ c ∧ c < t ^ (2 : ℕ)

lemma squaredEulerOrbitResponse_den_pos
    {t c u : ℝ} (hch : SquaredEulerOrbitChamber t c) (hu : 0 ≤ u) :
    0 < (t + u) ^ (2 : ℕ) + c := by
  have htu : 0 < t + u := by linarith [hch.1]
  nlinarith [sq_pos_of_pos htu, hch.2.1]

/-- Every chamber atom is strictly positive on the nonnegative radial ray. -/
theorem squaredEulerOrbitResponse_pos
    {t c u : ℝ} (hch : SquaredEulerOrbitChamber t c) (hu : 0 ≤ u) :
    0 < squaredEulerOrbitResponse t c u := by
  exact div_pos (by linarith [hch.1])
    (squaredEulerOrbitResponse_den_pos hch hu)

/-- Exact difference formula behind strict radial decrease. -/
theorem squaredEulerOrbitResponse_sub_eq
    {t c u v : ℝ} (hch : SquaredEulerOrbitChamber t c)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    squaredEulerOrbitResponse t c u - squaredEulerOrbitResponse t c v =
      (v - u) * ((t + u) * (t + v) - c) /
        (((t + u) ^ (2 : ℕ) + c) * ((t + v) ^ (2 : ℕ) + c)) := by
  have hdu := (squaredEulerOrbitResponse_den_pos hch hu).ne'
  have hdv := (squaredEulerOrbitResponse_den_pos hch hv).ne'
  rw [squaredEulerOrbitResponse, squaredEulerOrbitResponse]
  field_simp [hdu, hdv]
  ring

/-- Exact difference formula behind strict increase of the radius-weighted response. -/
theorem mul_squaredEulerOrbitResponse_sub_eq
    {t c u v : ℝ} (hch : SquaredEulerOrbitChamber t c)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v * squaredEulerOrbitResponse t c v -
        u * squaredEulerOrbitResponse t c u =
      (v - u) *
          (t * (t + u) * (t + v) + c * (t + u + v)) /
        (((t + u) ^ (2 : ℕ) + c) * ((t + v) ^ (2 : ℕ) + c)) := by
  have hdu := (squaredEulerOrbitResponse_den_pos hch hu).ne'
  have hdv := (squaredEulerOrbitResponse_den_pos hch hv).ne'
  rw [squaredEulerOrbitResponse, squaredEulerOrbitResponse]
  field_simp [hdu, hdv]
  ring

/-- A squared-zero orbit response is strictly decreasing on the nonnegative radial ray. -/
theorem strictAntiOn_squaredEulerOrbitResponse
    {t c : ℝ} (hch : SquaredEulerOrbitChamber t c) :
    StrictAntiOn (squaredEulerOrbitResponse t c) (Ici 0) := by
  intro u hu v hv huv
  have hu0 : 0 ≤ u := hu
  have hv0 : 0 ≤ v := hv
  have htu : 0 < t + u := by linarith [hch.1]
  have htv : 0 < t + v := by linarith [hch.1]
  have hprod : t ^ (2 : ℕ) < (t + u) * (t + v) := by
    have huv0 : 0 < v := lt_of_le_of_lt hu0 huv
    nlinarith [mul_nonneg hch.1.le hu0, mul_pos hch.1 huv0]
  have hnum : 0 < (v - u) * ((t + u) * (t + v) - c) :=
    mul_pos (sub_pos.mpr huv) (sub_pos.mpr (hch.2.2.trans hprod))
  have hden : 0 <
      ((t + u) ^ (2 : ℕ) + c) * ((t + v) ^ (2 : ℕ) + c) :=
    mul_pos (squaredEulerOrbitResponse_den_pos hch hu0)
      (squaredEulerOrbitResponse_den_pos hch hv0)
  rw [← sub_pos]
  rw [squaredEulerOrbitResponse_sub_eq hch hu0 hv0]
  exact div_pos hnum hden

/-- Multiplying a squared-zero response by its radius reverses the monotonicity strictly. -/
theorem strictMonoOn_mul_squaredEulerOrbitResponse
    {t c : ℝ} (hch : SquaredEulerOrbitChamber t c) :
    StrictMonoOn (fun u => u * squaredEulerOrbitResponse t c u) (Ici 0) := by
  intro u hu v hv huv
  have hu0 : 0 ≤ u := hu
  have hv0 : 0 ≤ v := hv
  have htu : 0 < t + u := by linarith [hch.1]
  have htv : 0 < t + v := by linarith [hch.1]
  have hcore : 0 <
      t * (t + u) * (t + v) + c * (t + u + v) := by
    have hfirst : 0 < t * (t + u) * (t + v) :=
      mul_pos (mul_pos hch.1 htu) htv
    have hsum : 0 ≤ t + u + v := by linarith [hch.1]
    have hsecond : 0 ≤ c * (t + u + v) :=
      mul_nonneg hch.2.1 hsum
    linarith
  have hnum : 0 < (v - u) *
      (t * (t + u) * (t + v) + c * (t + u + v)) :=
    mul_pos (sub_pos.mpr huv) hcore
  have hden : 0 <
      ((t + u) ^ (2 : ℕ) + c) * ((t + v) ^ (2 : ℕ) + c) :=
    mul_pos (squaredEulerOrbitResponse_den_pos hch hu0)
      (squaredEulerOrbitResponse_den_pos hch hv0)
  rw [← sub_pos]
  rw [mul_squaredEulerOrbitResponse_sub_eq hch hu0 hv0]
  exact div_pos hnum hden

/-! ## The unconditional Xi chamber -/

/-- Horizontal/vertical displacement difference for one actual Xi zero copy. -/
def xiSquaredEulerOrbitT (q : XiZeroCopy) : ℝ :=
  (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)

/-- Transverse squared-zero charge for one actual Xi zero copy. -/
def xiSquaredEulerOrbitCharge (q : XiZeroCopy) : ℝ :=
  4 * ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) * (q.1 : ℂ).im ^ (2 : ℕ)

/-- The open critical strip and the source height gap place every Xi squared-zero orbit in the
strict response chamber. -/
theorem xiSquaredEulerOrbit_mem_chamber (q : XiZeroCopy) :
    SquaredEulerOrbitChamber
      (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q) := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hu : u < 1 / 4 :=
    xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hv : 41 / 2 < v := by
    simpa only [v] using xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hv0 : 0 < v := by linarith
  have ht : 0 < v - u := by linarith
  have hc0 : 0 ≤ 4 * u * v := by positivity
  have hc_lt_v : 4 * u * v < v := by
    have hfour : 4 * u < 1 := by linarith
    nlinarith [mul_lt_mul_of_pos_right hfour hv0]
  have htlarge : 20 < v - u := by linarith
  have hv_lt : v < (v - u) + 1 / 4 := by linarith
  have hquarter_sq : (v - u) + 1 / 4 < (v - u) ^ (2 : ℕ) := by
    nlinarith
  change SquaredEulerOrbitChamber (v - u) (4 * u * v)
  exact ⟨ht, hc0, hc_lt_v.trans (hv_lt.trans hquarter_sq)⟩

/-- Radial response of one actual Xi squared-zero orbit. -/
def xiSquaredEulerOrbitResponse (q : XiZeroCopy) (u : ℝ) : ℝ :=
  squaredEulerOrbitResponse
    (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q) u

theorem xiSquaredEulerOrbitResponse_pos (q : XiZeroCopy)
    {u : ℝ} (hu : 0 ≤ u) :
    0 < xiSquaredEulerOrbitResponse q u :=
  squaredEulerOrbitResponse_pos (xiSquaredEulerOrbit_mem_chamber q) hu

theorem strictAntiOn_xiSquaredEulerOrbitResponse (q : XiZeroCopy) :
    StrictAntiOn (xiSquaredEulerOrbitResponse q) (Ici 0) :=
  strictAntiOn_squaredEulerOrbitResponse (xiSquaredEulerOrbit_mem_chamber q)

theorem strictMonoOn_mul_xiSquaredEulerOrbitResponse (q : XiZeroCopy) :
    StrictMonoOn (fun u => u * xiSquaredEulerOrbitResponse q u) (Ici 0) :=
  strictMonoOn_mul_squaredEulerOrbitResponse (xiSquaredEulerOrbit_mem_chamber q)

/-! ## Finite Xi packets -/

/-- A finite positive packet of actual Xi squared-zero orbit responses. -/
def xiSquaredEulerFiniteResponse (S : Finset XiZeroCopy) (u : ℝ) : ℝ :=
  ∑ q ∈ S, xiSquaredEulerOrbitResponse q u

/-- Every nonempty finite Xi packet has strictly positive response. -/
theorem xiSquaredEulerFiniteResponse_pos
    {S : Finset XiZeroCopy} (hS : S.Nonempty) {u : ℝ} (hu : 0 ≤ u) :
    0 < xiSquaredEulerFiniteResponse S u := by
  classical
  unfold xiSquaredEulerFiniteResponse
  exact Finset.sum_pos (fun q _ => xiSquaredEulerOrbitResponse_pos q hu) hS

/-- Strict radial decrease survives every nonempty finite Xi packet. -/
theorem strictAntiOn_xiSquaredEulerFiniteResponse
    {S : Finset XiZeroCopy} (hS : S.Nonempty) :
    StrictAntiOn (xiSquaredEulerFiniteResponse S) (Ici 0) := by
  classical
  intro u hu v hv huv
  unfold xiSquaredEulerFiniteResponse
  apply Finset.sum_lt_sum
  · intro q _hq
    exact (strictAntiOn_xiSquaredEulerOrbitResponse q hu hv huv).le
  · obtain ⟨q, hq⟩ := hS
    exact ⟨q, hq, strictAntiOn_xiSquaredEulerOrbitResponse q hu hv huv⟩

/-- Strict increase of the radius-weighted response survives every nonempty finite Xi packet. -/
theorem strictMonoOn_mul_xiSquaredEulerFiniteResponse
    {S : Finset XiZeroCopy} (hS : S.Nonempty) :
    StrictMonoOn (fun u => u * xiSquaredEulerFiniteResponse S u) (Ici 0) := by
  classical
  intro u hu v hv huv
  unfold xiSquaredEulerFiniteResponse
  change u * (∑ q ∈ S, xiSquaredEulerOrbitResponse q u) <
    v * (∑ q ∈ S, xiSquaredEulerOrbitResponse q v)
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro q _hq
    exact (strictMonoOn_mul_xiSquaredEulerOrbitResponse q hu hv huv).le
  · obtain ⟨q, hq⟩ := hS
    exact ⟨q, hq, strictMonoOn_mul_xiSquaredEulerOrbitResponse q hu hv huv⟩

/-! ## Exact two-point response-correlation law -/

/-- Cauchy response kernel generated by a scalar Euler-ray logarithmic derivative. -/
def eulerRayResponseKernel (Q : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (Q x + Q y) / (x + y)

/-- The two-point determinant factors into the decrease gap of `Q(x)/x` and the increase gap of
`x*Q(x)`. -/
theorem eulerRayResponseKernel_twoPoint_det_factor
    (Q : ℝ → ℝ) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    eulerRayResponseKernel Q x x * eulerRayResponseKernel Q y y -
        eulerRayResponseKernel Q x y ^ (2 : ℕ) =
      ((y * Q x - x * Q y) * (y * Q y - x * Q x)) /
        (x * y * (x + y) ^ (2 : ℕ)) := by
  rw [eulerRayResponseKernel, eulerRayResponseKernel,
    eulerRayResponseKernel]
  field_simp [hx, hy, hxy]
  ring

/-- **Abstract response-correlation cancellation.**  Opposite strict radial monotonicities force
every two-node Euler response determinant to be positive. -/
theorem eulerRayResponseKernel_twoPoint_det_pos
    (Q : ℝ → ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hdecrease : Q y / y < Q x / x)
    (hincrease : x * Q x < y * Q y) :
    0 < eulerRayResponseKernel Q x x * eulerRayResponseKernel Q y y -
      eulerRayResponseKernel Q x y ^ (2 : ℕ) := by
  have hy : 0 < y := hx.trans hxy
  have hsum : 0 < x + y := by positivity
  have hfirst : 0 < y * Q x - x * Q y := by
    rw [div_lt_div_iff₀ hy hx] at hdecrease
    nlinarith
  have hsecond : 0 < y * Q y - x * Q x := by linarith
  rw [eulerRayResponseKernel_twoPoint_det_factor Q hx.ne' hy.ne' hsum.ne']
  exact div_pos (mul_pos hfirst hsecond) (by positivity)

/-! ## Sharp three-node law for one orbit -/

/-- Scalar logarithmic derivative contributed by one squared-zero orbit. -/
def squaredEulerOrbitQ (t c x : ℝ) : ℝ :=
  x * squaredEulerOrbitResponse t c (x ^ (2 : ℕ))

/-- Euler response kernel contributed by one squared-zero orbit. -/
def squaredEulerOrbitKernel (t c x y : ℝ) : ℝ :=
  eulerRayResponseKernel (squaredEulerOrbitQ t c) x y

/-- Explicit determinant of a symmetric kernel on three nodes. -/
def symmetricThreePointDet (K : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  K x x * K y y * K z z + 2 * K x y * K x z * K y z -
    K x x * K y z ^ (2 : ℕ) - K y y * K x z ^ (2 : ℕ) - K z z * K x y ^ (2 : ℕ)

/-- Positive denominator attached to one radial node. -/
def squaredEulerOrbitDen (t c x : ℝ) : ℝ :=
  (t + x ^ (2 : ℕ)) ^ (2 : ℕ) + c

/-- Polynomial kernel obtained after clearing both orbit denominators. -/
def squaredEulerOrbitClearedKernel (t c x y : ℝ) : ℝ :=
  (x * y + t) * (x ^ (2 : ℕ) + t) * (y ^ (2 : ℕ) + t) +
    c * (x ^ (2 : ℕ) - x * y + y ^ (2 : ℕ) + t)

/-- The scalar aperture controlling the third exterior power of one orbit response. -/
def squaredEulerOrbitThreeAperture (t c x y z : ℝ) : ℝ :=
  let e1 := x + y + z
  let e2 := x * y + x * z + y * z
  let e3 := x * y * z
  (t ^ (2 : ℕ) + c) *
      (c - (e2 - t) ^ (2 : ℕ) - t * e1 ^ (2 : ℕ) + 2 * e1 * e3) -
    t * e3 ^ (2 : ℕ)

lemma squaredEulerOrbitDen_pos
    {t c x : ℝ} (hch : SquaredEulerOrbitChamber t c) :
    0 < squaredEulerOrbitDen t c x := by
  unfold squaredEulerOrbitDen
  have hxt : 0 < x ^ (2 : ℕ) + t := by nlinarith [sq_nonneg x, hch.1]
  nlinarith [sq_pos_of_pos hxt, hch.2.1]

/-- Exact polynomial congruence for one conjugate squared-zero pair. -/
theorem squaredEulerOrbitKernel_cleared
    {t c x y : ℝ} (hch : SquaredEulerOrbitChamber t c)
    (hx : 0 < x) (hy : 0 < y) :
    squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
        squaredEulerOrbitKernel t c x y =
      squaredEulerOrbitClearedKernel t c x y := by
  have hDx := (squaredEulerOrbitDen_pos (x := x) hch).ne'
  have hDy := (squaredEulerOrbitDen_pos (x := y) hch).ne'
  have hxy : x + y ≠ 0 := by positivity
  unfold squaredEulerOrbitKernel eulerRayResponseKernel squaredEulerOrbitQ
    squaredEulerOrbitResponse
  change squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
      ((x * ((t + x ^ (2 : ℕ)) / squaredEulerOrbitDen t c x) +
        y * ((t + y ^ (2 : ℕ)) / squaredEulerOrbitDen t c y)) / (x + y)) =
        squaredEulerOrbitClearedKernel t c x y
  field_simp [hDx, hDy, hxy]
  unfold squaredEulerOrbitDen squaredEulerOrbitClearedKernel
  ring

/-- Pure polynomial factorization of the cleared three-node determinant. -/
theorem squaredEulerOrbitClearedKernel_threePointDet_eq
    (t c x y z : ℝ) :
    symmetricThreePointDet (squaredEulerOrbitClearedKernel t c) x y z =
      c * ((y - x) * (z - x) * (z - y)) ^ (2 : ℕ) *
        squaredEulerOrbitThreeAperture t c x y z := by
  unfold symmetricThreePointDet squaredEulerOrbitClearedKernel
    squaredEulerOrbitThreeAperture
  ring

/-- Clearing the three node denominators is a positive diagonal congruence. -/
theorem squaredEulerOrbitKernel_threePointDet_cleared
    {t c x y z : ℝ} (hch : SquaredEulerOrbitChamber t c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    symmetricThreePointDet (squaredEulerOrbitClearedKernel t c) x y z =
      (squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
          squaredEulerOrbitDen t c z) ^ (2 : ℕ) *
        symmetricThreePointDet (squaredEulerOrbitKernel t c) x y z := by
  have hxx := squaredEulerOrbitKernel_cleared hch hx hx
  have hxy := squaredEulerOrbitKernel_cleared hch hx hy
  have hxz := squaredEulerOrbitKernel_cleared hch hx hz
  have hyy := squaredEulerOrbitKernel_cleared hch hy hy
  have hyz := squaredEulerOrbitKernel_cleared hch hy hz
  have hzz := squaredEulerOrbitKernel_cleared hch hz hz
  unfold symmetricThreePointDet
  rw [← hxx, ← hxy, ← hxz, ← hyy, ← hyz, ← hzz]
  ring

/-- Exact rational factorization of the single-orbit three-node determinant. -/
theorem squaredEulerOrbitKernel_threePointDet_eq
    {t c x y z : ℝ} (hch : SquaredEulerOrbitChamber t c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    symmetricThreePointDet (squaredEulerOrbitKernel t c) x y z =
      c * ((y - x) * (z - x) * (z - y)) ^ (2 : ℕ) *
          squaredEulerOrbitThreeAperture t c x y z /
        (squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
          squaredEulerOrbitDen t c z) ^ (2 : ℕ) := by
  have hscale := squaredEulerOrbitKernel_threePointDet_cleared hch hx hy hz
  have hfactor := squaredEulerOrbitClearedKernel_threePointDet_eq t c x y z
  have hden : (squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
      squaredEulerOrbitDen t c z) ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (mul_ne_zero
      (mul_ne_zero (squaredEulerOrbitDen_pos (x := x) hch).ne'
        (squaredEulerOrbitDen_pos (x := y) hch).ne')
      (squaredEulerOrbitDen_pos (x := z) hch).ne')
  apply (eq_div_iff hden).2
  calc
    symmetricThreePointDet (squaredEulerOrbitKernel t c) x y z *
        (squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
          squaredEulerOrbitDen t c z) ^ (2 : ℕ) =
      (squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
          squaredEulerOrbitDen t c z) ^ (2 : ℕ) *
        symmetricThreePointDet (squaredEulerOrbitKernel t c) x y z := by ring
    _ = symmetricThreePointDet (squaredEulerOrbitClearedKernel t c) x y z :=
      hscale.symm
    _ = c * ((y - x) * (z - x) * (z - y)) ^ (2 : ℕ) *
        squaredEulerOrbitThreeAperture t c x y z := hfactor

/-- The three-node aperture is strictly negative throughout the response chamber, independently
of the locations of the positive nodes. -/
theorem squaredEulerOrbitThreeAperture_neg
    {t c x y z : ℝ} (hch : SquaredEulerOrbitChamber t c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    squaredEulerOrbitThreeAperture t c x y z < 0 := by
  let e1 : ℝ := x + y + z
  let e2 : ℝ := x * y + x * z + y * z
  let e3 : ℝ := x * y * z
  have he2pos : 0 < e2 := by
    dsimp only [e2]
    positivity
  have he1sq : 3 * e2 ≤ e1 ^ (2 : ℕ) := by
    have hsquares :
        0 ≤ (x - y) ^ (2 : ℕ) + (x - z) ^ (2 : ℕ) + (y - z) ^ (2 : ℕ) := by positivity
    dsimp only [e1, e2]
    nlinarith
  have he2sq : 3 * e1 * e3 ≤ e2 ^ (2 : ℕ) := by
    have hsquares : 0 ≤
        (x * y - x * z) ^ (2 : ℕ) + (x * y - y * z) ^ (2 : ℕ) +
          (x * z - y * z) ^ (2 : ℕ) := by positivity
    dsimp only [e1, e2, e3]
    nlinarith
  have ht_e1 : 3 * t * e2 ≤ t * e1 ^ (2 : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_left he1sq hch.1.le]
  have hcross : 2 * e1 * e3 ≤ (2 / 3 : ℝ) * e2 ^ (2 : ℕ) := by
    nlinarith [he2sq]
  have hbracket :
      c - (e2 - t) ^ (2 : ℕ) - t * e1 ^ (2 : ℕ) + 2 * e1 * e3 < 0 := by
    nlinarith [hch.2.2, ht_e1, hcross,
      mul_nonneg hch.1.le he2pos.le, sq_nonneg e2]
  have hfactor : 0 < t ^ (2 : ℕ) + c := by
    nlinarith [sq_pos_of_pos hch.1, hch.2.1]
  have hmain := mul_neg_of_pos_of_neg hfactor hbracket
  have hlast : 0 ≤ t * e3 ^ (2 : ℕ) := mul_nonneg hch.1.le (sq_nonneg e3)
  change (t ^ (2 : ℕ) + c) *
      (c - (e2 - t) ^ (2 : ℕ) - t * e1 ^ (2 : ℕ) + 2 * e1 * e3) -
        t * e3 ^ (2 : ℕ) < 0
  linarith

/-- **Sharp single-orbit detector law.**  Every transverse chamber orbit is invisible at two
nodes but has negative determinant on every three distinct positive nodes. -/
theorem squaredEulerOrbitKernel_threePointDet_neg
    {t c x y z : ℝ} (hch : SquaredEulerOrbitChamber t c) (hc : 0 < c)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    symmetricThreePointDet (squaredEulerOrbitKernel t c) x y z < 0 := by
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := hy.trans hyz
  have hDelta : 0 < (y - x) * (z - x) * (z - y) := by
    have hxz : x < z := hxy.trans hyz
    positivity
  have hA := squaredEulerOrbitThreeAperture_neg hch hx hy hz
  have hnum :
      c * ((y - x) * (z - x) * (z - y)) ^ (2 : ℕ) *
        squaredEulerOrbitThreeAperture t c x y z < 0 := by
    exact mul_neg_of_pos_of_neg (mul_pos hc (sq_pos_of_pos hDelta)) hA
  rw [squaredEulerOrbitKernel_threePointDet_eq hch hx hy hz]
  have hdenpos : 0 <
      (squaredEulerOrbitDen t c x * squaredEulerOrbitDen t c y *
        squaredEulerOrbitDen t c z) ^ (2 : ℕ) := by
    exact sq_pos_of_pos (mul_pos
      (mul_pos (squaredEulerOrbitDen_pos (x := x) hch)
        (squaredEulerOrbitDen_pos (x := y) hch))
      (squaredEulerOrbitDen_pos (x := z) hch))
  exact div_neg_of_neg_of_pos hnum hdenpos

/-- One actual Xi orbit response kernel. -/
def xiSquaredEulerOrbitKernel (q : XiZeroCopy) (x y : ℝ) : ℝ :=
  squaredEulerOrbitKernel
    (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q) x y

/-- A genuinely off-critical Xi orbit has strictly positive transverse squared charge. -/
theorem xiSquaredEulerOrbitCharge_pos_of_ne_half
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < xiSquaredEulerOrbitCharge q := by
  have hdelta : 0 < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  have him : 0 < (q.1 : ℂ).im ^ (2 : ℕ) := by
    linarith [xiZeroCopy_fortyOne_div_two_lt_im_sq q]
  unfold xiSquaredEulerOrbitCharge
  positivity

/-! ## Confluent parity-jet charge law -/

/-- Zeroth reversed-Löwner jet moment of one squared orbit. -/
def squaredEulerOrbitReversedLoewnerMoment0 (t c X : ℝ) : ℝ :=
  ((t + X) ^ (2 : ℕ) - c) / (((t + X) ^ (2 : ℕ) + c) ^ (2 : ℕ))

/-- First reversed-Löwner jet moment of one squared orbit. -/
def squaredEulerOrbitReversedLoewnerMoment1 (t c X : ℝ) : ℝ :=
  (t + X) * ((t + X) ^ (2 : ℕ) - 3 * c) / (((t + X) ^ (2 : ℕ) + c) ^ (3 : ℕ))

/-- Second reversed-Löwner jet moment of one squared orbit. -/
def squaredEulerOrbitReversedLoewnerMoment2 (t c X : ℝ) : ℝ :=
  ((t + X) ^ (4 : ℕ) - 6 * (t + X) ^ (2 : ℕ) * c + c ^ (2 : ℕ)) /
    (((t + X) ^ (2 : ℕ) + c) ^ (4 : ℕ))

/-- **Exact confluent transverse-charge law.**  The first nonconstant `2 × 2` reversed-Löwner
jet determinant of one orbit is precisely its negative transverse charge divided by the fourth
power of the radial denominator. -/
theorem squaredEulerOrbit_reversedLoewnerJet_det_eq
    {t c X : ℝ} (hch : SquaredEulerOrbitChamber t c) (hX : 0 ≤ X) :
    squaredEulerOrbitReversedLoewnerMoment0 t c X *
        squaredEulerOrbitReversedLoewnerMoment2 t c X -
      squaredEulerOrbitReversedLoewnerMoment1 t c X ^ (2 : ℕ) =
        -c / (((t + X) ^ (2 : ℕ) + c) ^ (4 : ℕ)) := by
  have hden : 0 < (t + X) ^ (2 : ℕ) + c := by
    have htx : 0 < t + X := by linarith [hch.1]
    nlinarith [sq_pos_of_pos htx, hch.2.1]
  unfold squaredEulerOrbitReversedLoewnerMoment0
    squaredEulerOrbitReversedLoewnerMoment1
    squaredEulerOrbitReversedLoewnerMoment2
  field_simp [hden.ne']
  ring

/-- Positive transverse charge makes the confluent reversed-Löwner jet determinant strictly
negative at every nonnegative collision center. -/
theorem squaredEulerOrbit_reversedLoewnerJet_det_neg
    {t c X : ℝ} (hch : SquaredEulerOrbitChamber t c) (hc : 0 < c) (hX : 0 ≤ X) :
    squaredEulerOrbitReversedLoewnerMoment0 t c X *
        squaredEulerOrbitReversedLoewnerMoment2 t c X -
      squaredEulerOrbitReversedLoewnerMoment1 t c X ^ (2 : ℕ) < 0 := by
  rw [squaredEulerOrbit_reversedLoewnerJet_det_eq hch hX]
  have hden : 0 < (t + X) ^ (2 : ℕ) + c := by
    have htx : 0 < t + X := by linarith [hch.1]
    nlinarith [sq_pos_of_pos htx, hch.2.1]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hc) (pow_pos hden 4)

/-- Every off-critical actual Xi orbit is already detected by the first `2 × 2` confluent
reflection-parity jet determinant, at every nonnegative collision center. -/
theorem xiSquaredEulerOrbit_reversedLoewnerJet_det_neg
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {X : ℝ} (hX : 0 ≤ X) :
    squaredEulerOrbitReversedLoewnerMoment0
          (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q) X *
        squaredEulerOrbitReversedLoewnerMoment2
          (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q) X -
      squaredEulerOrbitReversedLoewnerMoment1
          (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q) X ^ (2 : ℕ) < 0 :=
  squaredEulerOrbit_reversedLoewnerJet_det_neg
    (xiSquaredEulerOrbit_mem_chamber q)
    (xiSquaredEulerOrbitCharge_pos_of_ne_half q hoff) hX

/-- **Actual-Xi sharpness theorem.**  Every off-critical Xi divisor orbit has negative response
determinant on every three ordered positive Euler nodes. -/
theorem xiSquaredEulerOrbitKernel_threePointDet_neg
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    symmetricThreePointDet (xiSquaredEulerOrbitKernel q) x y z < 0 := by
  exact squaredEulerOrbitKernel_threePointDet_neg
    (xiSquaredEulerOrbit_mem_chamber q)
    (xiSquaredEulerOrbitCharge_pos_of_ne_half q hoff) hx hxy hyz

/-- Finite Xi-packet logarithmic derivative on the positive Euler ray. -/
def xiSquaredEulerFiniteQ (S : Finset XiZeroCopy) (x : ℝ) : ℝ :=
  x * xiSquaredEulerFiniteResponse S (x ^ (2 : ℕ))

/-- Euler response kernel of a finite Xi squared-zero packet. -/
def xiSquaredEulerFiniteKernel (S : Finset XiZeroCopy) (x y : ℝ) : ℝ :=
  eulerRayResponseKernel (xiSquaredEulerFiniteQ S) x y

/-- Every nonempty finite actual-Xi packet has positive Euler-response diagonal. -/
theorem xiSquaredEulerFiniteKernel_diag_pos
    {S : Finset XiZeroCopy} (hS : S.Nonempty) {x : ℝ} (hx : 0 < x) :
    0 < xiSquaredEulerFiniteKernel S x x := by
  have hprofile := xiSquaredEulerFiniteResponse_pos hS (sq_nonneg x)
  have hdiag :
      xiSquaredEulerFiniteKernel S x x =
        xiSquaredEulerFiniteResponse S (x ^ (2 : ℕ)) := by
    rw [xiSquaredEulerFiniteKernel, eulerRayResponseKernel,
      xiSquaredEulerFiniteQ]
    field_simp [hx.ne']
  rw [hdiag]
  exact hprofile

/-- **Unconditional finite Xi two-node response theorem.**  Every pair of distinct positive Euler
nodes has strictly positive determinant, even when the packet contains off-critical zeros. -/
theorem xiSquaredEulerFiniteKernel_twoPoint_det_pos
    {S : Finset XiZeroCopy} (hS : S.Nonempty)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < xiSquaredEulerFiniteKernel S x x *
        xiSquaredEulerFiniteKernel S y y -
      xiSquaredEulerFiniteKernel S x y ^ (2 : ℕ) := by
  have hy : 0 < y := hx.trans hxy
  have hsq : x ^ (2 : ℕ) < y ^ (2 : ℕ) := by nlinarith
  have hdecreaseProfile :
      xiSquaredEulerFiniteResponse S (y ^ (2 : ℕ)) <
        xiSquaredEulerFiniteResponse S (x ^ (2 : ℕ)) :=
    strictAntiOn_xiSquaredEulerFiniteResponse hS
      (sq_nonneg x) (sq_nonneg y) hsq
  have hincreaseProfile :
      x ^ (2 : ℕ) * xiSquaredEulerFiniteResponse S (x ^ (2 : ℕ)) <
        y ^ (2 : ℕ) * xiSquaredEulerFiniteResponse S (y ^ (2 : ℕ)) :=
    strictMonoOn_mul_xiSquaredEulerFiniteResponse hS
      (sq_nonneg x) (sq_nonneg y) hsq
  have hdecrease :
      xiSquaredEulerFiniteQ S y / y < xiSquaredEulerFiniteQ S x / x := by
    simpa [xiSquaredEulerFiniteQ, hx.ne', hy.ne'] using hdecreaseProfile
  have hincrease :
      x * xiSquaredEulerFiniteQ S x < y * xiSquaredEulerFiniteQ S y := by
    simpa [xiSquaredEulerFiniteQ, pow_two, mul_assoc] using hincreaseProfile
  simpa only [xiSquaredEulerFiniteKernel] using
    eulerRayResponseKernel_twoPoint_det_pos
      (xiSquaredEulerFiniteQ S) hx hxy hdecrease hincrease

/-! ## Exact finite-packet charge/interference decomposition -/

/-- Polarized determinant interaction between two squared-orbit reversed-Löwner jet triples. -/
def squaredEulerOrbitReversedLoewnerCross
    (t c t' c' X : ℝ) : ℝ :=
  squaredEulerOrbitReversedLoewnerMoment0 t c X *
      squaredEulerOrbitReversedLoewnerMoment2 t' c' X +
    squaredEulerOrbitReversedLoewnerMoment0 t' c' X *
      squaredEulerOrbitReversedLoewnerMoment2 t c X -
    2 * squaredEulerOrbitReversedLoewnerMoment1 t c X *
      squaredEulerOrbitReversedLoewnerMoment1 t' c' X

/-- First reversed-Löwner determinant of a finite packet of squared orbits. -/
def squaredEulerPacketReversedLoewnerJetDet
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) : ℝ :=
  (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment0 (t i) (c i) X) *
      (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment2 (t i) (c i) X) -
    (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment1 (t i) (c i) X) ^ (2 : ℕ)

/-- Ordered off-diagonal interference between distinct squared orbits.  Each unordered pair is
counted twice, matching determinant polarization. -/
def squaredEulerPacketReversedLoewnerInterference
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (t c : ι → ℝ) (X : ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i,
    squaredEulerOrbitReversedLoewnerCross (t i) (c i) (t j) (c j) X

/-- Total transverse-charge debt of a finite squared-orbit packet at one collision center. -/
def squaredEulerPacketReversedLoewnerCharge
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) : ℝ :=
  ∑ i ∈ S, c i / (((t i + X) ^ (2 : ℕ) + c i) ^ (4 : ℕ))

/-- Determinant polarization: twice the packet determinant is the ordered sum of every self and
cross interaction. -/
theorem two_mul_squaredEulerPacketReversedLoewnerJetDet_eq_cross_sum
    {ι : Type*} (S : Finset ι) (t c : ι → ℝ) (X : ℝ) :
    2 * squaredEulerPacketReversedLoewnerJetDet S t c X =
      ∑ i ∈ S, ∑ j ∈ S,
        squaredEulerOrbitReversedLoewnerCross (t i) (c i) (t j) (c j) X := by
  let A02 := ∑ i ∈ S, ∑ j ∈ S,
    squaredEulerOrbitReversedLoewnerMoment0 (t i) (c i) X *
      squaredEulerOrbitReversedLoewnerMoment2 (t j) (c j) X
  let A20 := ∑ i ∈ S, ∑ j ∈ S,
    squaredEulerOrbitReversedLoewnerMoment0 (t j) (c j) X *
      squaredEulerOrbitReversedLoewnerMoment2 (t i) (c i) X
  let A11 := ∑ i ∈ S, ∑ j ∈ S,
    squaredEulerOrbitReversedLoewnerMoment1 (t i) (c i) X *
      squaredEulerOrbitReversedLoewnerMoment1 (t j) (c j) X
  have hswap : A02 = A20 := by
    dsimp only [A02, A20]
    rw [Finset.sum_comm]
  unfold squaredEulerPacketReversedLoewnerJetDet
    squaredEulerOrbitReversedLoewnerCross
  rw [show (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment1 (t i) (c i) X) ^ (2 : ℕ) =
      (∑ i ∈ S, squaredEulerOrbitReversedLoewnerMoment1 (t i) (c i) X) *
        (∑ j ∈ S, squaredEulerOrbitReversedLoewnerMoment1 (t j) (c j) X) by ring]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  change 2 * (A02 - A11) = _
  calc
    2 * (A02 - A11) = A02 + A20 - 2 * A11 := by rw [← hswap]; ring
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (squaredEulerOrbitReversedLoewnerMoment0 (t i) (c i) X *
            squaredEulerOrbitReversedLoewnerMoment2 (t j) (c j) X +
          squaredEulerOrbitReversedLoewnerMoment0 (t j) (c j) X *
            squaredEulerOrbitReversedLoewnerMoment2 (t i) (c i) X -
          2 * squaredEulerOrbitReversedLoewnerMoment1 (t i) (c i) X *
            squaredEulerOrbitReversedLoewnerMoment1 (t j) (c j) X) := by
      dsimp only [A02, A20, A11]
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := rfl

/-- The full ordered interaction sum splits exactly into self interactions and distinct-orbit
interference. -/
theorem squaredEulerPacketReversedLoewner_cross_sum_eq_self_add_interference
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (t c : ι → ℝ) (X : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S,
        squaredEulerOrbitReversedLoewnerCross (t i) (c i) (t j) (c j) X) =
      (∑ i ∈ S,
        squaredEulerOrbitReversedLoewnerCross (t i) (c i) (t i) (c i) X) +
        squaredEulerPacketReversedLoewnerInterference S t c X := by
  rw [squaredEulerPacketReversedLoewnerInterference, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_erase_add _ _ hi]
  ring

/-- A self interaction is exactly twice the negative transverse charge. -/
theorem squaredEulerOrbitReversedLoewnerCross_self_eq
    {t c X : ℝ} (hch : SquaredEulerOrbitChamber t c) (hX : 0 ≤ X) :
    squaredEulerOrbitReversedLoewnerCross t c t c X =
      -2 * (c / (((t + X) ^ (2 : ℕ) + c) ^ (4 : ℕ))) := by
  unfold squaredEulerOrbitReversedLoewnerCross
  rw [show squaredEulerOrbitReversedLoewnerMoment0 t c X *
          squaredEulerOrbitReversedLoewnerMoment2 t c X +
        squaredEulerOrbitReversedLoewnerMoment0 t c X *
          squaredEulerOrbitReversedLoewnerMoment2 t c X -
        2 * squaredEulerOrbitReversedLoewnerMoment1 t c X *
          squaredEulerOrbitReversedLoewnerMoment1 t c X =
      2 * (squaredEulerOrbitReversedLoewnerMoment0 t c X *
          squaredEulerOrbitReversedLoewnerMoment2 t c X -
        squaredEulerOrbitReversedLoewnerMoment1 t c X ^ (2 : ℕ)) by ring]
  rw [squaredEulerOrbit_reversedLoewnerJet_det_eq hch hX]
  ring

/-- **Exact finite-packet masking law.**  Twice the global confluent determinant is distinct-orbit
interference minus twice the sum of transverse self-charges.  This is the sharp boundary between
local off-critical detection and global masking. -/
theorem two_mul_squaredEulerPacketReversedLoewnerJetDet_eq_interference_sub_charge
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (t c : ι → ℝ) {X : ℝ}
    (hch : ∀ i ∈ S, SquaredEulerOrbitChamber (t i) (c i))
    (hX : 0 ≤ X) :
    2 * squaredEulerPacketReversedLoewnerJetDet S t c X =
      squaredEulerPacketReversedLoewnerInterference S t c X -
        2 * squaredEulerPacketReversedLoewnerCharge S t c X := by
  rw [two_mul_squaredEulerPacketReversedLoewnerJetDet_eq_cross_sum,
    squaredEulerPacketReversedLoewner_cross_sum_eq_self_add_interference]
  have hself :
      (∑ i ∈ S,
          squaredEulerOrbitReversedLoewnerCross (t i) (c i) (t i) (c i) X) =
        -2 * squaredEulerPacketReversedLoewnerCharge S t c X := by
    rw [squaredEulerPacketReversedLoewnerCharge, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [squaredEulerOrbitReversedLoewnerCross_self_eq (hch i hi) hX]
  rw [hself]
  ring

/-- Packet determinant is nonnegative exactly when cross-orbit interference pays the complete
transverse-charge debt. -/
theorem squaredEulerPacketReversedLoewnerJetDet_nonneg_iff_interference_ge_charge
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (t c : ι → ℝ) {X : ℝ}
    (hch : ∀ i ∈ S, SquaredEulerOrbitChamber (t i) (c i))
    (hX : 0 ≤ X) :
    0 ≤ squaredEulerPacketReversedLoewnerJetDet S t c X ↔
      2 * squaredEulerPacketReversedLoewnerCharge S t c X ≤
        squaredEulerPacketReversedLoewnerInterference S t c X := by
  have hmask := two_mul_squaredEulerPacketReversedLoewnerJetDet_eq_interference_sub_charge
    S t c hch hX
  constructor <;> intro h <;> nlinarith

end

end RHTower
