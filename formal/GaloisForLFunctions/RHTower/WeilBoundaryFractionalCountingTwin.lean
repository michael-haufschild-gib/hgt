import GaloisForLFunctions.RHTower.WeilBoundaryIntegerCountingRigidity
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope

/-!
# A `1/k`-integer counting function makes a producer a real-rooted twin

Let `lam` be full-cone Weil-positive with boundary measure `μ = μ_lam`, and let `k ≥ 1`.  Suppose
`k · μ((a,b]) ∈ ℕ` for all `a < b` in a set of full Lebesgue measure, and `μ` has no mass on
`(−1, 1)`.  Along the critical line this says that the `k`-th power of the completed exponential
`s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{−s}/log n)` has constant phase modulo `π` almost everywhere.

**Theorem** (`bigG_pow_eq_atomQ_of_fractional_counting`).  There are integers `m_j ≥ 0` and
ordinates `t_j ≥ 1` with `Σ m_j/t_j² < ∞` such that on `Re s > 1`

`(s(s−1)Γ_ℝ(s))^k · exp(Σ_{n≥2} k·lam(n) n^{−s}/log n) = K · Q(s)`,

where `Q = IntegerMassRigidity.atomQ m t` is entire, satisfies `Q(1−s) = Q(s)`, and vanishes only
at the points `½ ± i t_j`.  So `exp(Σ k·lam(n) n^{−s}/log n)` is a Dirichlet series with the
functional equation of `ζ^k` whose completion has all its zeros on the critical line: a real-rooted
twin of degree `k`.  For `k = 1` this is the Hamburger setting, and the companion theorem
`vonMangoldt_and_riemannHypothesis_of_integer_counting` concludes `lam = Λ`.

**Proof.**
* The scaled measure `k μ` has integer counting, so `μ` is a countable sum of point masses
  `m_j/k` with `m_j ∈ ℕ`, placed symmetrically at `±t_j` (`exists_isolating_interval`,
  `boundaryMeasure_singleton_neg`).
* The Poisson representation of the Weil function and the identity
  `Re(2w/(w² + t²)) = Re w (|w − it|⁻² + |w + it|⁻²)` give `Re Φ = Re A` on `Re s > 1`, where
  `A` is the atomic Herglotz series with masses `m_j/k`.  The difference is holomorphic with zero
  real part and real at `s = 2`, hence `Φ = A` (`weilFunction_eq_atomicPairSeries`).
* Then `(G^k)'/G^k = k A` is the atomic series with integer masses `m_j`, which is `Q'/Q`, so
  `G^k/Q` is constant on `Re s > 1` (`bigG_pow_eq_mul_atomQ`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate ENNReal NNReal
open Zeta23 GaloisForLFunctions

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz IntegerMassRigidity

/-! ## Atomic measures as sums over positive atoms -/

/-- A measure on `ℝ` concentrated on a countable symmetric set of atoms outside `(−1, 1)`
integrates as a sum over its positive atoms. -/
theorem lintegral_eq_tsum_pos_atoms {μ : Measure ℝ} (hSc : {x : ℝ | μ {x} ≠ 0}.Countable)
    (hSnull : μ {x : ℝ | μ {x} ≠ 0}ᶜ = 0) (hsym : ∀ x : ℝ, μ {-x} = μ {x})
    (hgap : μ (Ioo (-1) 1) = 0) (g : ℝ → ℝ≥0∞) :
    ∫⁻ r, g r ∂μ = ∑' x : {x : ℝ | μ {x} ≠ 0 ∧ 0 < x}, (g x + g (-x)) * μ {(x : ℝ)} := by
  set S := {x : ℝ | μ {x} ≠ 0} with hS
  set P := {x : ℝ | μ {x} ≠ 0 ∧ 0 < x} with hP
  set N := {x : ℝ | μ {x} ≠ 0 ∧ x < 0} with hN
  have hS1 : ∀ x ∈ S, 1 ≤ |x| := by
    intro x hx
    by_contra h
    have hmem : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp (lt_of_not_ge h)
    exact hx (measure_mono_null (singleton_subset_iff.mpr hmem) hgap)
  have hSPN : S = P ∪ N := by
    ext x
    simp only [hS, hP, hN, mem_setOf_eq, mem_union]
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inr ⟨hx, h⟩
      · exfalso; have := hS1 x hx; rw [h, abs_zero] at this; linarith
      · exact Or.inl ⟨hx, h⟩
    · rintro (h | h) <;> exact h.1
  have hPN : Disjoint P N := by
    rw [Set.disjoint_left]
    intro x hxP hxN
    linarith [hxP.2, hxN.2]
  have hneg : ∀ x : ℝ, x ∈ P ↔ (Equiv.neg ℝ) x ∈ N := by
    intro x
    simp only [hP, hN, mem_setOf_eq, Equiv.neg_apply, hsym x, neg_lt_zero]
  have hae : ∀ᵐ r ∂μ, r ∈ S := by
    rw [ae_iff]; exact hSnull
  conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
  rw [lintegral_countable g hSc]
  set F : ℝ → ℝ≥0∞ := fun y => g y * μ {y} with hF
  have h1 : ∑' y : S, g y * μ {(y : ℝ)} = ∑' y : P, F y + ∑' y : N, F y := by
    rw [show (∑' y : S, g y * μ {(y : ℝ)}) = ∑' y : S, F y from rfl, tsum_subtype,
      tsum_subtype, tsum_subtype, hSPN, indicator_union_of_disjoint hPN, ENNReal.tsum_add]
  have h2 : ∑' y : N, F y = ∑' x : P, F (-x) := by
    rw [← Equiv.tsum_eq (Equiv.subtypeEquiv (Equiv.neg ℝ) hneg) fun y : N => F y]
    rfl
  rw [h1, h2, ← ENNReal.tsum_add]
  congr 1
  funext x
  show g x * μ {(x : ℝ)} + g (-x) * μ {-(x : ℝ)} = _
  rw [hsym, add_mul]

/-- Reindexing an `ℝ≥0∞`-valued sum over a countable set of reals along its encoding. -/
theorem tsum_decode₂_eq_ennreal {P : Set ℝ} [Encodable P] (k : P → ℝ≥0∞) (G : ℝ → ℝ≥0∞) :
    ∑' j : ℕ, ((Encodable.decode₂ P j).elim 0 fun x => k x) *
        G ((Encodable.decode₂ P j).elim 1 fun x => (x : ℝ)) =
      ∑' x : P, k x * G x := by
  set F : ℕ → ℝ≥0∞ := fun j => ((Encodable.decode₂ P j).elim 0 fun x => k x) *
    G ((Encodable.decode₂ P j).elim 1 fun x => (x : ℝ)) with hF
  have hsupp : Function.support F ⊆ range (Encodable.encode : P → ℕ) := by
    intro j hj
    rcases hd : Encodable.decode₂ P j with _ | x
    · exfalso; apply hj; simp [hF, hd]
    · exact ⟨x, Encodable.mem_decode₂.mp hd⟩
  have h := Function.Injective.tsum_eq (Encodable.encode_injective (α := P)) hsupp
  rw [← h]
  congr 1
  funext x
  simp [hF]

/-! ## An atomic boundary measure determines the Weil function -/

/-- **Poisson route to the atomic identity.**  If the boundary measure of a full-cone producer is
the symmetric atomic measure with masses `c_j ≥ 0` at `±t_j` (`t_j ≥ 1`, `Σ c_j/t_j² < ∞`), then
the Weil function is the atomic Herglotz series on `Re s > 1`. -/
theorem weilFunction_eq_atomicPairSeries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {c t : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => c j / t j ^ 2)
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      ∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))) :
    ∀ s : ℂ, 1 < s.re → weilFunction lam s = atomicPairSeries (fun j => Real.pi * c j) t s := by
  set A := atomicPairSeries (fun j => Real.pi * c j) t with hA
  have hsumA : Summable fun j => |Real.pi * c j| / t j ^ 2 := by
    refine (hsum.mul_left Real.pi).congr fun j => ?_
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le (hc j))]
    ring
  -- equality of real parts on `Re s > 1`
  have hre : ∀ s : ℂ, 1 < s.re → (weilFunction lam s).re = (A s).re := by
    intro s hs
    set w : ℂ := s - 1 / 2 with hwdef
    have hw0 : 0 < w.re := by rw [hwdef]; norm_num; linarith
    have hP := lintegral_poissonDensity_eq hW hs
    rw [← hwdef, hrep w hw0] at hP
    have hΦ0 : 0 ≤ (weilFunction lam s).re / w.re :=
      div_nonneg (re_weilFunction_nonneg hW hs) hw0.le
    have hfin : ∀ j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))
        ≠ ⊤ := fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_ne_top.mpr ⟨poissonDensity_ne_top _ _, poissonDensity_ne_top _ _⟩)
    have hreal := congrArg ENNReal.toReal hP
    rw [ENNReal.tsum_toReal_eq hfin, ENNReal.toReal_ofReal hΦ0] at hreal
    have hterm : ∀ j, (ENNReal.ofReal (c j) * (poissonDensity w (t j) +
        poissonDensity w (-(t j)))).toReal =
        c j * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 + ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2) := by
      intro j
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc j),
        ENNReal.toReal_add (poissonDensity_ne_top _ _) (poissonDensity_ne_top _ _)]
      congr 1
    simp_rw [hterm] at hreal
    have hAre : (A s).re = w.re * ∑' j, c j * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 +
        ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2) := by
      have hAeq : A s = ∑' j, ((c j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
        rw [hA, atomicPairSeries, ← tsum_mul_left]
        refine tsum_congr fun j => ?_
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        rw [← hwdef]
        push_cast
        field_simp
      have hsumC : Summable fun j => ((c j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
        refine Summable.of_norm_bounded
          ((hsum.mul_left (2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2)))) fun j => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j)]
        have := norm_two_mul_div_le hw0 (hone j)
        calc c j * ‖2 * w / (w ^ 2 + (t j : ℂ) ^ 2)‖
            ≤ c j * (2 * ‖w‖ * ((4 + 4 * w.im ^ 2 / w.re ^ 2) / t j ^ 2)) :=
              mul_le_mul_of_nonneg_left this (hc j)
          _ = 2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2) * (c j / t j ^ 2) := by ring
      rw [hAeq, Complex.re_tsum hsumC, ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [Complex.re_ofReal_mul, re_two_mul_div hw0]
      ring
    rw [hAre, hreal, mul_div_assoc', mul_div_cancel_left₀ _ hw0.ne']
  -- the difference is constant on `Re s > 1`
  set U : Set ℂ := {z | 1 < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 1
  have hAd := differentiableOn_atomicPairSeries hone hsumA
  have hgd : DifferentiableOn ℂ (fun z => weilFunction lam z - A z) U := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hAz : DifferentiableAt ℂ A z := hAd.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        show 1 / 2 < z.re; linarith))
    exact ((differentiableAt_weilFunction hW hz').sub hAz).differentiableWithinAt
  have hgre : ∀ z ∈ U, (weilFunction lam z - A z).re = 0 := by
    intro z hz
    rw [Complex.sub_re, hre z hz, sub_self]
  have h2U : (2 : ℂ) ∈ U := by show 1 < (2 : ℂ).re; norm_num
  -- the constant is real at `s = 2`, hence zero
  have him : (weilFunction lam 2 - A 2).im = 0 := by
    have hL : (LSeries (lamC lam) 2).im = 0 := by
      rw [LSeries, Complex.im_tsum (summable_term_lamC hW (by norm_num))]
      refine (tsum_congr fun n => ?_).trans tsum_zero
      rw [LSeries.term_def]
      split_ifs with hn
      · simp
      · rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, lamC]
        rw [show ((n : ℂ) ^ 2) = (((n : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_div]
        exact Complex.ofReal_im _
    have hA2 : (A 2).im = 0 := by
      rw [hA, atomicPairSeries]
      have hreal : (∑' j, ((Real.pi * c j : ℝ) : ℂ) / ((2 - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)) =
          ((∑' j, (Real.pi * c j) / ((3 / 2) ^ 2 + t j ^ 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        refine tsum_congr fun j => ?_
        push_cast
        ring
      rw [hreal]
      have : (2 * ((2 : ℂ) - 1 / 2) / (Real.pi : ℂ)) = ((2 * (3 / 2) / Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this, ← Complex.ofReal_mul, Complex.ofReal_im]
    rw [Complex.sub_im, hA2, weilFunction]
    simp only [Complex.sub_im, Complex.add_im, hL]
    rw [show (2 : ℂ) / 2 = 1 by norm_num, Complex.digamma_one]
    simp
  have hzero : weilFunction lam 2 - A 2 = 0 :=
    Complex.ext (by rw [hgre 2 h2U]; rfl) (by rw [him]; rfl)
  intro s hs
  have hc' := eq_of_re_eq_zero hU hUc hgd hgre hs h2U
  rw [hzero, sub_eq_zero] at hc'
  exact hc'

/-! ## The `k`-th power of the completed exponential -/

theorem atomicPairSeries_div_mul (m : ℕ → ℕ) (t : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (k : ℂ) * atomicPairSeries (fun j => Real.pi * m j / k) t s =
      atomicPairSeries (fun j => Real.pi * m j) t s := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold atomicPairSeries
  rw [mul_left_comm, ← tsum_mul_left]
  congr 2
  funext j
  push_cast
  field_simp

/-- **`G^k` is the atom product on `Re s > 1`.**  If the Weil function is the atomic series with
masses `m_j/k`, then `G^k = K Q` with `K = G(2)^k/Q(2)`. -/
theorem bigG_pow_eq_mul_atomQ {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {k : ℕ} (hk : 0 < k)
    (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j / k) t s)
    {s : ℂ} (hs : 1 < s.re) :
    bigG lam s ^ k = (bigG lam 2 ^ k / atomQ m t 2) * atomQ m t s := by
  set V : Set ℂ := {z : ℂ | 1 < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : Convex ℝ V := convex_halfSpace_re_gt 1
  have hQd := differentiable_atomQ hone hsum
  have hQne : ∀ z ∈ V, atomQ m t z ≠ 0 := fun z hz =>
    atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne (by
      have : (1 : ℝ) < z.re := hz; intro h; rw [h] at this; norm_num at this))
  set r : ℂ → ℂ := fun z => bigG lam z ^ k / atomQ m t z with hr
  have hGk : ∀ z : ℂ, 1 < z.re → HasDerivAt (fun w => bigG lam w ^ k)
      ((k : ℂ) * bigG lam z ^ (k - 1) * (bigG lam z * (1 / z + 1 / (z - 1) +
        gammaRealLogConnection z - LSeries (lamTwo lam) z))) z := by
    intro z hz
    have h := (hasDerivAt_bigG hsl hz).pow k
    refine HasDerivAt.congr_deriv (f := fun w => bigG lam w ^ k) h ?_
    ring
  have hrd : DifferentiableOn ℂ r V := fun z hz =>
    ((hGk z hz).differentiableAt.div (hQd z) (hQne z hz)).differentiableWithinAt
  have hderiv : Set.EqOn (deriv r) 0 V := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hz1 : ∀ i : AtomIndex m, z ≠ atomAt t i := ne_atomAt_of_re_ne (by
      intro h; rw [h] at hz'; norm_num at hz')
    have hL := logDeriv_atomQ hone hsum hz1
    rw [logDeriv_apply] at hL
    have hQ' : deriv (atomQ m t) z = atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t z := by
      rw [← hL]; field_simp [hQne z hz]
    have hd : HasDerivAt r (((k : ℂ) * bigG lam z ^ (k - 1) * (bigG lam z * (1 / z + 1 / (z - 1) +
        gammaRealLogConnection z - LSeries (lamTwo lam) z)) * atomQ m t z -
          bigG lam z ^ k * deriv (atomQ m t) z) / atomQ m t z ^ 2) z :=
      (hGk z hz').div (hQd z).hasDerivAt (hQne z hz)
    have hze : 1 / z + 1 / (z - 1) + gammaRealLogConnection z - LSeries (lamTwo lam) z =
        atomicPairSeries (fun j => Real.pi * m j / k) t z := by
      rw [← hid z hz']
      unfold zetaArchimedeanDatum gammaRealLogConnection
      ring
    have hpow : (k : ℂ) * bigG lam z ^ (k - 1) * bigG lam z = (k : ℂ) * bigG lam z ^ k := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [pow_succ]
      ring
    rw [hd.deriv, hQ', hze, ← atomicPairSeries_div_mul m t hk z]
    simp only [Pi.zero_apply]
    rw [div_eq_zero_iff]
    left
    calc (k : ℂ) * bigG lam z ^ (k - 1) * (bigG lam z *
          atomicPairSeries (fun j => Real.pi * m j / k) t z) * atomQ m t z -
          bigG lam z ^ k * ((k : ℂ) * atomicPairSeries (fun j => Real.pi * m j / k) t z *
            atomQ m t z)
        = ((k : ℂ) * bigG lam z ^ (k - 1) * bigG lam z) *
            atomicPairSeries (fun j => Real.pi * m j / k) t z * atomQ m t z -
          (k : ℂ) * bigG lam z ^ k * atomicPairSeries (fun j => Real.pi * m j / k) t z *
            atomQ m t z := by ring
      _ = 0 := by rw [hpow]; ring
  have h2 : (2 : ℂ) ∈ V := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hc := hVo.is_const_of_deriv_eq_zero hVc.isPreconnected hrd hderiv hs h2
  simp only [hr] at hc
  have hQs := hQne s hs
  rw [div_eq_iff hQs] at hc
  rw [hc]

/-! ## The main theorem -/

/-- **A `1/k`-integer counting function makes the producer a real-rooted twin.**  Let `lam` be
full-cone Weil-positive and `k ≥ 1`.  Suppose `k · μ_lam((a,b]) ∈ ℕ` for all `a < b` in a set of
full Lebesgue measure, and `μ_lam` has no mass on `(−1, 1)`.  Then there are integers `m_j` and
ordinates `t_j ≥ 1` with `Σ m_j/t_j² < ∞` such that `G^k = K·Q` on `Re s > 1`, where
`G(s) = s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{−s}/log n)` and `Q = atomQ m t` is entire, symmetric under
`s ↦ 1 − s`, and vanishes only on the critical line. -/
theorem bigG_pow_eq_atomQ_of_fractional_counting {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {k : ℕ} (hk : 0 < k) {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b →
      ∃ n : ℕ, (k : ℝ≥0∞) * boundaryMeasure hW (Ioc a b) = n)
    (hgap : boundaryMeasure hW (Ioo (-1) 1) = 0) :
    ∃ (m : ℕ → ℕ) (t : ℕ → ℝ), (∀ j, 1 ≤ t j) ∧ (Summable fun j => (m j : ℝ) / t j ^ 2) ∧
      ∀ s : ℂ, 1 < s.re → bigG lam s ^ k = (bigG lam 2 ^ k / atomQ m t 2) * atomQ m t s := by
  set μ := boundaryMeasure hW with hμ
  set ν : Measure ℝ := (k : ℝ≥0∞) • μ with hν
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hνapp : ∀ A, ν A = (k : ℝ≥0∞) * μ A := fun A => by simp [hν]
  have hfinν : ∀ a b : ℝ, ν (Ioo a b) ≠ ∞ := fun a b => by
    rw [hνapp]; exact ENNReal.mul_ne_top hktop (boundaryMeasure_Ioo_ne_top hW a b)
  have hcountν : ∀ a ∈ Y, ∀ b ∈ Y, a < b → ∃ n : ℕ, ν (Ioc a b) = n := fun a ha b hb hab => by
    obtain ⟨n, hn⟩ := hcount a ha b hb hab
    exact ⟨n, by rw [hνapp]; exact hn⟩
  obtain ⟨hSc, hSnull⟩ := atoms_countable_and_compl_null hfinν hY hcountν
  have hint : ∀ x, ∃ n : ℕ, ν {x} = n := fun x => by
    obtain ⟨_, _, _, _, _, hn⟩ := exists_isolating_interval hfinν hY hcountν x
    exact hn
  choose kk hkk using hint
  have hzero : ∀ A, μ A = 0 ↔ ν A = 0 := fun A => by
    rw [hνapp, mul_eq_zero]; simp [hk0]
  have hSet : {x : ℝ | μ {x} ≠ 0} = {x : ℝ | ν {x} ≠ 0} := by
    ext x; simp only [mem_setOf_eq, ne_eq, hzero]
  have hSc' : {x : ℝ | μ {x} ≠ 0}.Countable := hSet ▸ hSc
  have hSnull' : μ {x : ℝ | μ {x} ≠ 0}ᶜ = 0 := by rw [hzero, hSet]; exact hSnull
  have hsym : ∀ x : ℝ, μ {-x} = μ {x} := fun x => boundaryMeasure_singleton_neg hW x
  have hrepr := lintegral_eq_tsum_pos_atoms hSc' hSnull' hsym hgap
  set P := {x : ℝ | μ {x} ≠ 0 ∧ 0 < x} with hP
  have hPc : P.Countable := hSc'.mono fun x hx => hx.1
  have hP1 : ∀ x ∈ P, 1 ≤ x := by
    intro x hx
    by_contra h
    have hmem : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.2], lt_of_not_ge h⟩
    exact hx.1 (measure_mono_null (singleton_subset_iff.mpr hmem) hgap)
  have hmass : ∀ x, μ {x} = ENNReal.ofReal ((kk x : ℝ) / k) := by
    intro x
    have h := hkk x
    rw [hνapp] at h
    rw [ENNReal.ofReal_div_of_pos hkR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ← h,
      mul_comm, ENNReal.mul_div_cancel_right hk0 hktop]
  haveI : Encodable P := hPc.toEncodable
  set t : ℕ → ℝ := fun j => (Encodable.decode₂ P j).elim 1 fun x => (x : ℝ) with ht
  set m : ℕ → ℕ := fun j => (Encodable.decode₂ P j).elim 0 fun x => kk x with hm
  have hone : ∀ j, 1 ≤ t j := by
    intro j
    simp only [ht]
    rcases Encodable.decode₂ P j with _ | x
    · simp
    · exact hP1 x x.2
  -- summability of `m_j / t_j²`
  have hsum : Summable fun j => (m j : ℝ) / t j ^ 2 := by
    have hconv : (fun j => (m j : ℝ) / t j ^ 2) =
        fun j => (m j : ℝ) * (fun r : ℝ => 1 / r ^ 2) (t j) := by
      funext j; simp [div_eq_mul_inv]
    rw [hconv]
    refine (summable_decode₂_iff (fun x : P => kk x) (fun r : ℝ => 1 / r ^ 2)).mpr ?_
    set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (1 / (1 + r ^ 2)) with hg
    have hfinite : ∑' x : P, (g x + g (-x)) * μ {(x : ℝ)} ≠ ∞ := by
      rw [← hrepr g]; exact (lintegral_inv_one_add_sq_lt_top hW).ne
    have hsumE := ENNReal.summable_toReal hfinite
    have hterm : ∀ x : P, ((g x + g (-x)) * μ {(x : ℝ)}).toReal =
        (kk x : ℝ) * (2 / k * (1 / (1 + (x : ℝ) ^ 2))) := by
      intro x
      simp only [hg, neg_sq]
      rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
      field_simp
      ring
    simp_rw [hterm] at hsumE
    have hsumE' : Summable fun x : P => (kk x : ℝ) * (2 * (1 / (1 + (x : ℝ) ^ 2))) := by
      refine (hsumE.mul_left (k : ℝ)).congr fun x => ?_
      field_simp
    refine hsumE'.of_nonneg_of_le (fun x => by positivity) fun x => ?_
    have hx1 := hP1 x x.2
    have hk0' : (0 : ℝ) ≤ kk x := Nat.cast_nonneg _
    apply mul_le_mul_of_nonneg_left _ hk0'
    show 1 / (x : ℝ) ^ 2 ≤ 2 * (1 / (1 + (x : ℝ) ^ 2))
    have hx2 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := by nlinarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the Poisson representation in atomic form
  have hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      ∑' j, ENNReal.ofReal ((m j : ℝ) / k) *
        (poissonDensity w (t j) + poissonDensity w (-(t j))) := by
    intro w _
    rw [← hμ, hrepr fun r => poissonDensity w r]
    have h := tsum_decode₂_eq_ennreal (P := P) (fun x : P => ENNReal.ofReal ((kk x : ℝ) / k))
      (fun r : ℝ => poissonDensity w r + poissonDensity w (-r))
    rw [show (∑' x : P, (poissonDensity w x + poissonDensity w (-x)) * μ {(x : ℝ)}) =
        ∑' x : P, ENNReal.ofReal ((kk x : ℝ) / k) * (poissonDensity w x + poissonDensity w (-x))
        from tsum_congr fun x => by rw [hmass, mul_comm], ← h]
    refine tsum_congr fun j => ?_
    simp only [hm, ht]
    rcases Encodable.decode₂ P j with _ | x
    · simp
    · rfl
  have hid0 := weilFunction_eq_atomicPairSeries hW (c := fun j => (m j : ℝ) / k)
    (fun j => by positivity) hone
    ((hsum.div_const (k : ℝ)).congr fun j => by ring) hrep
  have hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j / k) t s := by
    intro s hs
    have h := hid0 s hs
    have hfun : lamTwo lam = lamC lam := by
      funext n
      rw [lamC, lamTwo]
      split_ifs <;> simp
    have hc : (fun j => Real.pi * ((m j : ℝ) / k)) = fun j => Real.pi * m j / k := by
      funext j; ring
    rw [hc] at h
    rw [← h, weilFunction, zetaArchimedeanDatum, hfun]
  refine ⟨m, t, hone, hsum, fun s hs => ?_⟩
  exact bigG_pow_eq_mul_atomQ hk hone hsum
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hid hs

/-- **Real-rooted twin form.**  Under the hypotheses of
`bigG_pow_eq_atomQ_of_fractional_counting`, the function `G^k` agrees on `Re s > 1` with an
entire function `Ĝ` satisfying `Ĝ(1 − s) = Ĝ(s)` whose zeros all lie on `Re s = ½`. -/
theorem exists_realRooted_twin_of_fractional_counting {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {k : ℕ} (hk : 0 < k) {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b →
      ∃ n : ℕ, (k : ℝ≥0∞) * boundaryMeasure hW (Ioc a b) = n)
    (hgap : boundaryMeasure hW (Ioo (-1) 1) = 0) :
    ∃ Ghat : ℂ → ℂ, Differentiable ℂ Ghat ∧ (∀ s, Ghat (1 - s) = Ghat s) ∧
      (∀ s : ℂ, s.re ≠ 1 / 2 → Ghat s ≠ 0) ∧ ∀ s : ℂ, 1 < s.re → bigG lam s ^ k = Ghat s := by
  obtain ⟨m, t, hone, hsum, hG⟩ :=
    bigG_pow_eq_atomQ_of_fractional_counting hW hk hY hcount hgap
  have hQ2 : atomQ m t 2 ≠ 0 :=
    atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne (by norm_num))
  have hG2 : bigG lam 2 ^ k ≠ 0 := pow_ne_zero _ (bigG_ne_zero lam (by norm_num))
  refine ⟨fun s => (bigG lam 2 ^ k / atomQ m t 2) * atomQ m t s,
    (differentiable_atomQ hone hsum).const_mul _, fun s => by simp only [atomQ_one_sub hone hsum],
    fun s hs => mul_ne_zero (div_ne_zero hG2 hQ2) (atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne hs)),
    hG⟩

end RHTower.WeilSpectral

end
