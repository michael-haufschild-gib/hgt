import GaloisForLFunctions.BezoutValuationIncidence.CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity

/-!
# All-Depth Hilbert Dilation Cube and Hypercube Gram Factorization (Tool 1, Part II)

This module completes **Tool 1** by lifting the all-depth coherent Euler–Dirichlet operator
factorization from pointwise primitives and step sources to the full-line Hilbert space `SoninL2`
and deriving the exact $2^{\omega(P)} \times 2^{\omega(P)}$ hypercube Gram quadratic form
factorization across all multiplicative depths $0 \le \omega(m_1), \omega(m_2) \le \omega(P)$
simultaneously:

1. **Linearity and Group Law of `rayDilate` on `SoninL2` (§1)**:
   Establishes `rayDilate_one`, `rayDilate_add`, `rayDilate_smul`, `rayDilate_sum`,
   `rayDilate_rayDilate`, and the general scale-ratio inner product identity
   (`re_inner_rayDilate_inv`):
   $$\operatorname{Re}\bigl\langle D_{a^{-1}} f_r,\; D_{b^{-1}} f_r \bigr\rangle_{\operatorname{SoninL2}}
     = \operatorname{pmRamanujanDilationProfile}\Bigl(r, hr, \frac{a}{b}\Bigr)
     \qquad (\forall a, b > 0).$$

2. **All-Depth Coherent `SoninL2` Hilbert Operator Factorization (§2)**:
   For any $\varepsilon > 0$, any squarefree integer $P$, and any base modulus $r > 1$ coprime to
   $P$, summing the weighted step vectors across all $2^{\omega(P)}$ divisors $m \mid P$ (spanning
   all multiplicative depths $\omega(mr) = \omega(r) + \omega(m)$ simultaneously) factors into the
   local Euler product `pmEulerCubeFactor ε P` times the pure Dirichlet dilation polynomial on
   `SoninL2` (`all_depth_coherent_pmStepVectorTotal_eq`):
   $$\sum_{m \in P.\text{divisors}} Y_\varepsilon(mr) \bullet f_{mr}
     = \bigl(\operatorname{pmEulerCubeFactor}(\varepsilon, P)\,Y_\varepsilon(r)\bigr) \bullet
       \sum_{d \in P.\text{divisors}}
         \mu(d)\,d^{-\frac{1}{2}-\varepsilon} \bullet D_{d^{-1}} f_r.$$

3. **All-Depth $2^{\omega(P)} \times 2^{\omega(P)}$ Hypercube Gram-to-Dilation-Profile Identity (§3)**:
   Taking the `SoninL2` inner product of `all_depth_coherent_pmStepVectorTotal_eq` with itself
   collapses the entire $2^{\omega(P)} \times 2^{\omega(P)}$ Gram quadratic form of
   `pmRamanujanPrimitiveGram` (and of `pmRamanujanEnergyCenteredGram` whenever `¬ IsPrimePow r`)
   into the pure Dirichlet quadratic form of the continuous dilation profile $\Phi_r(d_1 / d_2)$
   (`all_depth_coherent_primitiveGram_cube_eq`,
   `all_depth_coherent_energyCenteredGram_cube_eq_of_not_isPrimePow`):
   $$\sum_{m_1 \mid P} \sum_{m_2 \mid P} Y_\varepsilon(m_1 r)\,Y_\varepsilon(m_2 r)\,\mathcal{G}(m_1 r, m_2 r)
     = \bigl(\operatorname{pmEulerCubeFactor}(\varepsilon, P)\bigr)^2\,Y_\varepsilon(r)^2
       \sum_{d_1 \mid P} \sum_{d_2 \mid P}
         \mu(d_1)\,\mu(d_2)\,d_1^{-\frac{1}{2}-\varepsilon}\,d_2^{-\frac{1}{2}-\varepsilon}\,
         \Phi_r\Bigl(\frac{d_1}{d_2}\Bigr),$$
   with zero residual base-mode shift or cross-term defect outside $\Phi_r(d_1 / d_2)$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ## §1. Linearity, Group Law, and Inner-Product Calculus of `rayDilate` on `SoninL2` -/

/-- At unit scale `v = 1`, `rayDilate 1` is the identity operator on `SoninL2`. -/
@[simp]
theorem rayDilate_one (f : SoninL2) : rayDilate 1 f = f := by
  rw [rayDilate_of_pos zero_lt_one]
  apply Lp.ext
  filter_upwards [dilation_ae 1 zero_lt_one f] with x hx
  rw [hx, Real.sqrt_one, Complex.ofReal_one, one_mul, one_mul]

/-- For `v > 0`, `rayDilate v` is additive on `SoninL2`. -/
theorem rayDilate_add {v : ℝ} (hv : 0 < v) (f g : SoninL2) :
    rayDilate v (f + g) = rayDilate v f + rayDilate v g := by
  rw [rayDilate_of_pos hv, rayDilate_of_pos hv, rayDilate_of_pos hv, map_add]

/-- For `v > 0`, `rayDilate v` is `ℂ`-homogeneous on `SoninL2`. -/
theorem rayDilate_smul {v : ℝ} (hv : 0 < v) (c : ℂ) (f : SoninL2) :
    rayDilate v (c • f) = c • rayDilate v f := by
  rw [rayDilate_of_pos hv, rayDilate_of_pos hv, (dilation v hv).map_smul]

/-- For `v > 0`, `rayDilate v` commutes with finite sums in `SoninL2`. -/
theorem rayDilate_sum {v : ℝ} (hv : 0 < v) {ι : Type*} (s : Finset ι) (g : ι → SoninL2) :
    rayDilate v (∑ i ∈ s, g i) = ∑ i ∈ s, rayDilate v (g i) := by
  rw [rayDilate_of_pos hv]
  simpa only [← rayDilate_of_pos hv] using map_sum (dilation v hv) g s

/-- **Multiplicative Group Law for `rayDilate`**:
For all `u, v > 0` and `f : SoninL2`, `rayDilate u (rayDilate v f) = rayDilate (u * v) f`. -/
theorem rayDilate_rayDilate {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (f : SoninL2) :
    rayDilate u (rayDilate v f) = rayDilate (u * v) f := by
  rw [rayDilate_of_pos hu, rayDilate_of_pos hv, rayDilate_of_pos (mul_pos hu hv),
    dilation_dilation hu hv f]

/-- **General Scale-Ratio Inner Product Identity on `SoninL2`**:
For any modulus `r > 1` and any positive scales `a, b > 0`, the real part of the `SoninL2` inner
product between `rayDilate a⁻¹ (pmRamanujanStepVector r hr)` and
`rayDilate b⁻¹ (pmRamanujanStepVector r hr)` equals `pmRamanujanDilationProfile r hr (a / b)`. -/
theorem re_inner_rayDilate_inv {r : ℕ} (hr : 1 < r) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (inner ℂ (rayDilate a⁻¹ (pmRamanujanStepVector r hr))
      (rayDilate b⁻¹ (pmRamanujanStepVector r hr))).re =
      pmRamanujanDilationProfile r hr (a / b) := by
  let f := pmRamanujanStepVector r hr
  rw [rayDilate_of_pos (inv_pos.mpr ha), rayDilate_of_pos (inv_pos.mpr hb)]
  have h := (dilation a ha).inner_map_map
    (dilation a⁻¹ (inv_pos.mpr ha) f) (dilation b⁻¹ (inv_pos.mpr hb) f)
  rw [dilation_dilation_inv, dilation_dilation] at h
  have hray : rayDilate (a / b) f =
      dilation (a * b⁻¹) (mul_pos ha (inv_pos.mpr hb)) f := by
    simpa only [div_eq_mul_inv] using rayDilate_of_pos (div_pos ha hb) f
  rw [pmRamanujanDilationProfile, hray, ← h]

/-! ## §2. All-Depth Coherent `SoninL2` Hilbert Operator Factorization -/

/-- Total-domain wrapper for `pmRamanujanStepVector`, equal to `pmRamanujanStepVector q hq` when
`1 < q` and `0` otherwise. -/
def pmStepVectorTotal (q : ℕ) : SoninL2 :=
  if hq : 1 < q then pmRamanujanStepVector q hq else 0

theorem pmStepVectorTotal_of_one_lt {q : ℕ} (hq : 1 < q) :
    pmStepVectorTotal q = pmRamanujanStepVector q hq := dif_pos hq

theorem re_inner_pmStepVectorTotal {q s : ℕ} (hq : 1 < q) (hs : 1 < s) :
    (inner ℂ (pmStepVectorTotal q) (pmStepVectorTotal s)).re =
      pmRamanujanPrimitiveGram q s := by
  rw [pmStepVectorTotal_of_one_lt hq, pmStepVectorTotal_of_one_lt hs]
  exact congrArg Complex.re (inner_pmRamanujanStepVector hq hs)

/-- **Single-Prime Cross-Depth Euler Operator Identity for `pmStepVectorTotal`**:
For `ε > 0`, prime `p`, `r > 1`, and `¬ p ∣ r`, pairing depth `ω(r)` with depth `ω(pr)` applies the
local Euler operator `(p^{1+ε} / (p^{1+ε} - 1)) (I - p^{-1/2-ε} rayDilate p⁻¹)` to
`(pmRealRamanujanWeight ε r : ℂ) • pmStepVectorTotal r`. -/
theorem cross_depth_pmStepVectorTotal_prime_pair_eq {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) :
    (pmRealRamanujanWeight ε r : ℂ) • pmStepVectorTotal r +
        (pmRealRamanujanWeight ε (p * r) : ℂ) • pmStepVectorTotal (p * r) =
      (((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) : ℝ) : ℂ) •
        ((pmRealRamanujanWeight ε r : ℂ) • pmStepVectorTotal r -
          (((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) •
            rayDilate (p : ℝ)⁻¹ ((pmRealRamanujanWeight ε r : ℂ) • pmStepVectorTotal r)) := by
  have hpr1 : 1 < p * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [pmStepVectorTotal_of_one_lt hr, pmStepVectorTotal_of_one_lt hpr1,
    ← pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight hε r,
    ← pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight hε (p * r),
    cross_depth_pmRamanujanStepVector_prime_pair_eq hε hp hr hpr,
    pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight hε r,
    rayDilate_smul (inv_pos.mpr hp0), rayDilate_of_pos (inv_pos.mpr hp0)]
  rw [smul_sub, smul_smul, smul_sub, smul_smul, smul_smul, smul_smul]
  congr 2 <;> (push_cast; ring)

/-- Helper: divisor sum splitting under multiplication by a prime `p ∤ Q`. -/
private theorem sum_divisors_prime_mul' {α : Type*} [AddCommMonoid α] (F : ℕ → α)
    {p Q : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q) :
    (∑ d ∈ (p * Q).divisors, F d) = ∑ d ∈ Q.divisors, (F d + F (p * d)) := by
  classical
  rw [(hp.coprime_iff_not_dvd.mpr hpQ).divisors_mul]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  trans ∑ x ∈ p.divisors ×ˢ Q.divisors, F (x.1 * x.2)
  · exact Finset.sum_attach (p.divisors ×ˢ Q.divisors) (fun x : ℕ × ℕ => F (x.1 * x.2))
  rw [Finset.sum_product, hp.divisors, Finset.sum_pair hp.ne_one.symm]
  simp only [one_mul, Finset.sum_add_distrib]

/-- **All-Depth Coherent `SoninL2` Hilbert Step-Vector Factorization (`0 ≤ ω(m) ≤ ω(P)`)**:
For any `ε > 0`, any squarefree `P`, and any base modulus `r > 1` coprime to `P`, summing the
weighted step vectors `(pmRealRamanujanWeight ε (m * r) : ℂ) • pmStepVectorTotal (m * r)`
coherently across all `2^{ω(P)}` divisors `m ∣ P` factors out
`pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r` and transforms the sum into the pure Dirichlet
dilation polynomial on `SoninL2`:
`∑_{d ∣ P} (μ(d) d^{-1/2-ε}) • rayDilate d⁻¹ (pmRamanujanStepVector r hr)`. -/
theorem all_depth_coherent_pmStepVectorTotal_eq {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hr : 1 < r) (hPr : Nat.Coprime P r) :
    (∑ m ∈ P.divisors,
        (pmRealRamanujanWeight ε (m * r) : ℂ) • pmStepVectorTotal (m * r)) =
      (((pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r : ℝ) : ℂ)) •
        ∑ d ∈ P.divisors,
          (((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
            rayDilate (d : ℝ)⁻¹ (pmRamanujanStepVector r hr) := by
  induction P using induction_on_primes with
  | zero => exact (_root_.not_squarefree_zero hP).elim
  | one =>
    simp [pmEulerCubeFactor_one, moebiusReal, pmStepVectorTotal_of_one_lt hr, rayDilate_one]
  | prime_mul p Q hp ih =>
    have hQ : Squarefree Q := hP.of_mul_right
    have hQ0 : Q ≠ 0 := by intro h; subst h; exact _root_.not_squarefree_zero hQ
    have hpQ : ¬ p ∣ Q := fun h =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hP)) h
    have hQr : Nat.Coprime Q r := (Nat.coprime_mul_iff_left.mp hPr).2
    have hpr : ¬ p ∣ r := hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp hPr).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp_inv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
    rw [sum_divisors_prime_mul' _ hp hpQ]
    have hpair :
        ∀ m ∈ Q.divisors,
          (pmRealRamanujanWeight ε (m * r) : ℂ) • pmStepVectorTotal (m * r) +
              (pmRealRamanujanWeight ε (p * m * r) : ℂ) • pmStepVectorTotal (p * m * r) =
            (((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) : ℝ) : ℂ) •
              ((pmRealRamanujanWeight ε (m * r) : ℂ) • pmStepVectorTotal (m * r) -
                (((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) •
                  rayDilate (p : ℝ)⁻¹
                    ((pmRealRamanujanWeight ε (m * r) : ℂ) • pmStepVectorTotal (m * r))) := by
      intro m hm
      have hm_pos : 0 < m := Nat.pos_of_mem_divisors hm
      have hmr1 : 1 < m * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hm_pos)
      have hmQ : m ∣ Q := Nat.dvd_of_mem_divisors hm
      have hpm : ¬ p ∣ m := fun h => hpQ (h.trans hmQ)
      have hpmr : ¬ p ∣ m * r := by
        rw [hp.dvd_mul]
        exact not_or.mpr ⟨hpm, hpr⟩
      simpa only [mul_assoc p m r] using
        cross_depth_pmStepVectorTotal_prime_pair_eq hε hp hmr1 hpmr
    rw [Finset.sum_congr rfl hpair, ← Finset.smul_sum, Finset.sum_sub_distrib,
      ← Finset.smul_sum, ← rayDilate_sum hp_inv, ih hQ hQr,
      rayDilate_smul hp_inv, rayDilate_sum hp_inv]
    rw [pmEulerCubeFactor_prime_mul ε hp hQ0 hpQ, sum_divisors_prime_mul' _ hp hpQ]
    let E_p : ℂ := (((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) : ℝ) : ℂ)
    let E_Q : ℂ := (((pmEulerCubeFactor ε Q * pmRealRamanujanWeight ε r : ℝ) : ℂ))
    let c_p : ℂ := (((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)
    let S_Q : SoninL2 :=
      ∑ d ∈ Q.divisors,
        (((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
          rayDilate (d : ℝ)⁻¹ (pmRamanujanStepVector r hr)
    have hcomb :
        ∑ x ∈ Q.divisors,
            rayDilate (p : ℝ)⁻¹
              ((((moebiusReal x * (x : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
                rayDilate (x : ℝ)⁻¹ (pmRamanujanStepVector r hr)) =
          ∑ x ∈ Q.divisors,
            (((moebiusReal x * (x : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
              rayDilate ((p * x : ℕ) : ℝ)⁻¹ (pmRamanujanStepVector r hr) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_mem_divisors hd)
      rw [rayDilate_smul hp_inv, rayDilate_rayDilate hp_inv (inv_pos.mpr hd_pos)]
      congr 2
      rw [Nat.cast_mul, mul_inv]
    rw [hcomb]
    have hsum_eq :
        S_Q - c_p •
          ∑ x ∈ Q.divisors,
            (((moebiusReal x * (x : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
              rayDilate ((p * x : ℕ) : ℝ)⁻¹ (pmRamanujanStepVector r hr) =
        ∑ d ∈ Q.divisors,
          ((((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
              rayDilate (d : ℝ)⁻¹ (pmRamanujanStepVector r hr) +
            (((moebiusReal (p * d) * ((p * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
              rayDilate ((p * d : ℕ) : ℝ)⁻¹ (pmRamanujanStepVector r hr)) := by
      dsimp only [S_Q, c_p]
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hd
      have hpd : ¬ p ∣ d := fun h => hpQ (h.trans hdQ)
      have hmu : moebiusReal (p * d) = -moebiusReal d := by
        simpa [moebiusReal, hpd] using Sieve.moebius_prime_mul (e := d) hp
      have hd0 : (0 : ℝ) ≤ d := by positivity
      have hcoeff :
          (((moebiusReal (p * d) * ((p * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) =
            -((((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) *
              (((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ))) := by
        have hR :
            moebiusReal (p * d) * ((p * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) - ε) =
              -((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) * (moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε))) := by
          rw [hmu, Nat.cast_mul, Real.mul_rpow hp0.le hd0]
          ring
        exact_mod_cast hR
      rw [hcoeff, smul_smul, neg_smul, ← sub_eq_add_neg]
    have hpull :
        E_p • (E_Q • S_Q - c_p • (E_Q •
          ∑ x ∈ Q.divisors,
            (((moebiusReal x * (x : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
              rayDilate ((p * x : ℕ) : ℝ)⁻¹ (pmRamanujanStepVector r hr))) =
        (E_p * E_Q) •
          (S_Q - c_p •
            ∑ x ∈ Q.divisors,
              (((moebiusReal x * (x : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
                rayDilate ((p * x : ℕ) : ℝ)⁻¹ (pmRamanujanStepVector r hr)) := by
      rw [smul_sub, smul_smul, smul_smul, smul_smul, smul_sub, smul_smul]
      congr 2
      ring
    change E_p • (E_Q • S_Q - c_p • (E_Q • _)) = _
    rw [hpull, hsum_eq]
    congr 1
    dsimp [E_p, E_Q]
    push_cast
    ring

/-! ## §3. All-Depth $2^{\omega(P)} \times 2^{\omega(P)}$ Hypercube Gram Factorization -/

/-- Helper: real part of the `SoninL2` norm-squared of a finite real-weighted sum of vectors. -/
private theorem re_inner_sum_ofReal_smul {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : ι → SoninL2) :
    (inner ℂ (∑ i ∈ s, (a i : ℂ) • v i) (∑ j ∈ s, (a j : ℂ) • v j)).re =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * (inner ℂ (v i) (v j)).re := by
  rw [sum_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  simp [Complex.mul_re, mul_assoc]

/-- **All-Depth $2^{\omega(P)} \times 2^{\omega(P)}$ Hypercube Pronic Gram Factorization**:
For any `ε > 0`, any squarefree `P`, and any base modulus `r > 1` coprime to `P`, the full
$2^{\omega(P)} \times 2^{\omega(P)}$ Gram quadratic form of `pmRamanujanPrimitiveGram` across all
divisors `m₁, m₂ ∣ P` (spanning all multiplicative depths `0 ≤ ω(m₁), ω(m₂) ≤ ω(P)`
simultaneously) equals `(pmEulerCubeFactor ε P)² Y_ε(r)²` times the pure Dirichlet quadratic form
of the continuous dilation profile `pmRamanujanDilationProfile r hr (d₁ / d₂)`:
$$
\begin{aligned}
&\sum_{m_1 \in P.\text{divisors}} \sum_{m_2 \in P.\text{divisors}}
  Y_\varepsilon(m_1 r)\,Y_\varepsilon(m_2 r)\,\mathcal{G}(m_1 r, m_2 r) \\
&= \bigl(\operatorname{pmEulerCubeFactor}(\varepsilon, P)\bigr)^2\,Y_\varepsilon(r)^2
  \sum_{d_1 \in P.\text{divisors}} \sum_{d_2 \in P.\text{divisors}}
    \mu(d_1)\,\mu(d_2)\,d_1^{-\frac{1}{2}-\varepsilon}\,d_2^{-\frac{1}{2}-\varepsilon}\,
    \Phi_r\Bigl(\frac{d_1}{d_2}\Bigr).
\end{aligned}
$$ -/
theorem all_depth_coherent_primitiveGram_cube_eq {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hr : 1 < r) (hPr : Nat.Coprime P r) :
    (∑ m₁ ∈ P.divisors, ∑ m₂ ∈ P.divisors,
        pmRealRamanujanWeight ε (m₁ * r) * pmRealRamanujanWeight ε (m₂ * r) *
          pmRamanujanPrimitiveGram (m₁ * r) (m₂ * r)) =
      pmEulerCubeFactor ε P ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
        ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) := by
  let L : SoninL2 :=
    ∑ m ∈ P.divisors, (pmRealRamanujanWeight ε (m * r) : ℂ) • pmStepVectorTotal (m * r)
  let R_sum : SoninL2 :=
    ∑ d ∈ P.divisors,
      (((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) •
        rayDilate (d : ℝ)⁻¹ (pmRamanujanStepVector r hr)
  let c : ℝ := pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r
  have hLR : L = (c : ℂ) • R_sum := all_depth_coherent_pmStepVectorTotal_eq hε hP hr hPr
  have h_inner : (inner ℂ L L).re = (inner ℂ ((c : ℂ) • R_sum) ((c : ℂ) • R_sum)).re := by
    rw [hLR]
  have hL :
      (inner ℂ L L).re =
        ∑ m₁ ∈ P.divisors, ∑ m₂ ∈ P.divisors,
          pmRealRamanujanWeight ε (m₁ * r) * pmRealRamanujanWeight ε (m₂ * r) *
            pmRamanujanPrimitiveGram (m₁ * r) (m₂ * r) := by
    dsimp only [L]
    rw [re_inner_sum_ofReal_smul]
    refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
    have hm₁_pos : 0 < m₁ := Nat.pos_of_mem_divisors hm₁
    have hm₂_pos : 0 < m₂ := Nat.pos_of_mem_divisors hm₂
    have hm₁r : 1 < m₁ * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hm₁_pos)
    have hm₂r : 1 < m₂ * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hm₂_pos)
    rw [re_inner_pmStepVectorTotal hm₁r hm₂r]
  have hR :
      (inner ℂ ((c : ℂ) • R_sum) ((c : ℂ) • R_sum)).re =
        pmEulerCubeFactor ε P ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
          ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
            (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
              (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
              pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) := by
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    dsimp only [R_sum, c]
    rw [re_inner_sum_ofReal_smul]
    have hsum_congr :
        (∑ i ∈ P.divisors, ∑ j ∈ P.divisors,
            moebiusReal i * (i : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
              (moebiusReal j * (j : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
              (inner ℂ (rayDilate (i : ℝ)⁻¹ (pmRamanujanStepVector r hr))
                (rayDilate (j : ℝ)⁻¹ (pmRamanujanStepVector r hr))).re) =
          ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
            (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
              (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
              pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) := by
      refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
      have hd₁_pos : (0 : ℝ) < d₁ := by exact_mod_cast (Nat.pos_of_mem_divisors hd₁)
      have hd₂_pos : (0 : ℝ) < d₂ := by exact_mod_cast (Nat.pos_of_mem_divisors hd₂)
      rw [re_inner_rayDilate_inv hr hd₁_pos hd₂_pos]
    rw [hsum_congr]
    ring
  rw [← hL, h_inner, hR]

/-- **All-Depth $2^{\omega(P)} \times 2^{\omega(P)}$ Hypercube Energy-Centered Gram Factorization
for Composite Non-Prime-Power Base Moduli**:
Whenever `¬ IsPrimePow r` (`r > 1`), every multiple `m * r` (`m ∣ P`) is also a non-prime-power, so
all von Mangoldt centering terms vanish and `pmRamanujanEnergyCenteredGram` satisfies the exact same
all-depth hypercube factorization into `pmRamanujanDilationProfile r hr (d₁ / d₂)`. -/
theorem all_depth_coherent_energyCenteredGram_cube_eq_of_not_isPrimePow {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hr : 1 < r) (hrp : ¬ IsPrimePow r) (hPr : Nat.Coprime P r) :
    (∑ m₁ ∈ P.divisors, ∑ m₂ ∈ P.divisors,
        pmRealRamanujanWeight ε (m₁ * r) * pmRealRamanujanWeight ε (m₂ * r) *
          pmRamanujanEnergyCenteredGram (m₁ * r) (m₂ * r)) =
      pmEulerCubeFactor ε P ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
        ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) := by
  rw [← all_depth_coherent_primitiveGram_cube_eq hε hP hr hPr]
  refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
  have hm₁_pos : 0 < m₁ := Nat.pos_of_mem_divisors hm₁
  have hm₂_pos : 0 < m₂ := Nat.pos_of_mem_divisors hm₂
  have hm₁r : 1 < m₁ * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hm₁_pos)
  have hm₂r : 1 < m₂ * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hm₂_pos)
  have hΛ₁ : vonMangoldt (m₁ * r) = 0 := by
    rw [vonMangoldt_eq_zero_iff]
    intro h
    exact hrp (h.dvd (dvd_mul_left r m₁) (by omega))
  have hΛ₂ : vonMangoldt (m₂ * r) = 0 := by
    rw [vonMangoldt_eq_zero_iff]
    intro h
    exact hrp (h.dvd (dvd_mul_left r m₂) (by omega))
  have hec := pmRamanujanPrimitiveGram_eq_energyCentered hm₁r hm₂r
  rw [hΛ₁, hΛ₂, mul_zero, zero_add] at hec
  rw [hec]

/-- **All-Depth Hypercube Dilation-Profile Diagonal Evaluation (`d₁ = d₂`)**:
On the diagonal `d₁ = d₂ = d` of the Dirichlet dilation-profile quadratic form over `d ∣ P`
(`P` squarefree), `μ(d)² = 1` and `Φ_r(d / d) = Φ_r(1) = G(r, r)`, so the diagonal sum evaluates
identically to `(∑_{d ∣ P} d^{-1-2ε}) G(r, r)`. -/
theorem all_depth_dilationProfile_cube_diag_sum_eq (ε : ℝ)
    {P r : ℕ} (hP : Squarefree P) (hr : 1 < r) :
    (∑ d ∈ P.divisors,
        (moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
          (moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
          pmRamanujanDilationProfile r hr ((d : ℝ) / d)) =
      (∑ d ∈ P.divisors, (d : ℝ) ^ (-1 - 2 * ε)) * pmRamanujanPrimitiveGram r r := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_mem_divisors hd)
  have hdsq : Squarefree d := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hmu : moebiusReal d ^ 2 = 1 := by
    dsimp [moebiusReal]
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq
  have hrpow :
      (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) =
        (d : ℝ) ^ (-1 - 2 * ε) := by
    rw [← Real.rpow_add hd_pos]
    congr 1; ring
  rw [div_self hd_pos.ne', pmRamanujanDilationProfile_one hr]
  linear_combination
    (d : ℝ) ^ (-1 - 2 * ε) * pmRamanujanPrimitiveGram r r * hmu +
      moebiusReal d ^ 2 * pmRamanujanPrimitiveGram r r * hrpow

/-! ## §4. Depth-Stratified Alternating Shell Decomposition & Energy-Centered Operator Factorization -/

/-- For any squarefree integer `d`, its real Möbius weight `moebiusReal d` is determined purely by
its multiplicative depth `cardDistinctFactors d = ω(d)`:
`moebiusReal d = (-1) ^ cardDistinctFactors d`. -/
theorem moebiusReal_eq_neg_one_pow_cardDistinctFactors {d : ℕ} (hd : Squarefree d) :
    moebiusReal d = (-1 : ℝ) ^ cardDistinctFactors d := by
  have hω : cardDistinctFactors d = cardFactors d :=
    (cardDistinctFactors_eq_cardFactors_iff_squarefree hd.ne_zero).mpr hd
  dsimp [moebiusReal]
  rw [hω, ArithmeticFunction.moebius_apply_of_squarefree hd]
  push_cast
  rfl

/-- For any divisor `d ∣ P` of a squarefree integer `P`, the multiplicative depth satisfies
`cardDistinctFactors d ≤ cardDistinctFactors P`. -/
theorem cardDistinctFactors_le_of_dvd_squarefree {P d : ℕ} (hP : Squarefree P)
    (hd : d ∈ P.divisors) :
    cardDistinctFactors d ≤ cardDistinctFactors P := by
  have hd_dvd : d ∣ P := Nat.dvd_of_mem_divisors hd
  have hd_sq : Squarefree d := hP.squarefree_of_dvd hd_dvd
  rw [(cardDistinctFactors_eq_cardFactors_iff_squarefree hd_sq.ne_zero).mpr hd_sq,
    (cardDistinctFactors_eq_cardFactors_iff_squarefree hP.ne_zero).mpr hP]
  rcases hd_dvd with ⟨q, rfl⟩
  have hq0 : q ≠ 0 := right_ne_zero_of_mul hP.ne_zero
  rw [ArithmeticFunction.cardFactors_mul hd_sq.ne_zero hq0]
  exact Nat.le_add_right _ _

/-- **Depth-Stratified Alternating Shell Decomposition (`sum_divisors_moebiusReal_eq_alternating_depth_shells`)**:
For any squarefree integer `P` and any function `F : ℕ → ℝ`, the Möbius-weighted sum over
`P.divisors` stratifies by exact multiplicative depth `k = ω(d) = cardDistinctFactors d` into an
alternating sum over `0 ≤ k ≤ ω(P)` where every divisor in the depth-`k` shell carries the uniform
sign `(-1)^k`:
$$
\sum_{d \in P.\text{divisors}} \mu(d)\,F(d) =
  \sum_{k=0}^{\omega(P)} (-1)^k \sum_{\substack{d \in P.\text{divisors} \\ \omega(d) = k}} F(d).
$$ -/
theorem sum_divisors_moebiusReal_eq_alternating_depth_shells {P : ℕ} (hP : Squarefree P)
    (F : ℕ → ℝ) :
    (∑ d ∈ P.divisors, moebiusReal d * F d) =
      ∑ k ∈ Finset.range (cardDistinctFactors P + 1),
        (-1 : ℝ) ^ k *
          ∑ d ∈ P.divisors.filter (fun d => cardDistinctFactors d = k), F d := by
  have hmaps :
      ∀ d ∈ P.divisors, cardDistinctFactors d ∈ Finset.range (cardDistinctFactors P + 1) := by
    intro d hd
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact cardDistinctFactors_le_of_dvd_squarefree hP hd
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_filter] at hd
  have hdsq : Squarefree d := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd.1)
  rw [moebiusReal_eq_neg_one_pow_cardDistinctFactors hdsq, hd.2]

/-- **All-Depth Alternating Shell Singularity Cancellation (`all_depth_alternating_shell_singularity_cancellation`)**:
When summed coherently across all multiplicative depths `0 ≤ k ≤ ω(P)` simultaneously, the
alternating depth-shell Dirichlet polynomial cancels the Euler cube singularity factor
`pmEulerCubeFactor ε P = ∏_{p ∣ P} p^{1+ε}/(p^{1+ε}-1)` to `1`:
$$
\operatorname{pmEulerCubeFactor}(\varepsilon, P)
  \sum_{k=0}^{\omega(P)} (-1)^k
    \sum_{\substack{d \in P.\text{divisors} \\ \omega(d) = k}} d^{-1-\varepsilon} = 1.
$$ -/
theorem all_depth_alternating_shell_singularity_cancellation {ε : ℝ} (hε : 0 < ε)
    {P : ℕ} (hP : Squarefree P) :
    pmEulerCubeFactor ε P *
      (∑ k ∈ Finset.range (cardDistinctFactors P + 1),
        (-1 : ℝ) ^ k *
          ∑ d ∈ P.divisors.filter (fun d => cardDistinctFactors d = k),
            (d : ℝ) ^ (-1 - ε)) = 1 := by
  rw [← sum_divisors_moebiusReal_eq_alternating_depth_shells hP]
  exact pmEulerCubeFactor_mul_dirichlet_moebius_sum_eq_one hε hP

/-- **Cross-Depth (`ω(r) = k ↔ ω(pr) = k + 1`) Energy-Centered Operator Factorization**:
Pairing a base modulus `r > 1` with its prime multiple `p * r` (`p ∤ r`) directly on the
energy-centered primitive `pmRamanujanEnergyCenteredPrimitive` annihilates the depth-`(k+1)`
von Mangoldt term (`Λ(pr) = 0`) and factors the oscillatory part into the Euler-shifted difference
operator at base modulus `r`:
$$
Y_\varepsilon(r)\,S_r^{\text{ec}}(N) + Y_\varepsilon(pr)\,S_{pr}^{\text{ec}}(N) =
  Y_\varepsilon(r)\,\Lambda(r) +
  \frac{p^{1+\varepsilon}}{p^{1+\varepsilon} - 1}\,Y_\varepsilon(r)\,
    \Bigl(\operatorname{Re} S_r(N) - p^{-\varepsilon}\,\operatorname{Re} S_r(\lfloor N / p \rfloor)\Bigr).
$$ -/
theorem cross_depth_pmRamanujanEnergyCenteredPrimitive_prime_pair_eq {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) (N : ℕ) :
    pmRealRamanujanWeight ε r * pmRamanujanEnergyCenteredPrimitive r N +
      pmRealRamanujanWeight ε (p * r) * pmRamanujanEnergyCenteredPrimitive (p * r) N =
    pmRealRamanujanWeight ε r * vonMangoldt r +
      ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)) * pmRealRamanujanWeight ε r *
        ((pmRamanujanPrimitive r N).re -
          (p : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / p)).re) := by
  have hΛ : vonMangoldt (p * r) = 0 :=
    vonMangoldt_mul_eq_zero_of_coprime (hp.coprime_iff_not_dvd.mpr hpr) hp.one_lt hr
  have hprim := cross_depth_pmRamanujanPrimitive_prime_pair_eq hε hp hpr N
  unfold pmRamanujanEnergyCenteredPrimitive
  rw [hΛ, add_zero]
  linarith

/-- **All-Depth Coherent Energy-Centered Operator Factorization (`all_depth_coherent_pmRamanujanEnergyCenteredPrimitive_eq`)**:
For any `ε > 0`, any squarefree `P`, and any base modulus `r > 1` coprime to `P`, summing the
energy-centered operator `pmRamanujanEnergyCenteredPrimitive (m * r) N` across all `2^{ω(P)}`
divisors `m ∣ P` annihilates `Λ(m * r)` at every positive depth `ω(m) ≥ 1` (`m > 1`), isolating the
single base von Mangoldt term `Y_ε(r) Λ(r)` at `m = 1` and factoring the oscillatory sum across all
multiplicative depths `0 ≤ k ≤ ω(P)` into the alternating depth-shell Dirichlet difference operator:
$$
\begin{aligned}
\sum_{m \in P.\text{divisors}} Y_\varepsilon(mr)\,S_{mr}^{\text{ec}}(N)
&= Y_\varepsilon(r)\,\Lambda(r) +
  \operatorname{pmEulerCubeFactor}(\varepsilon, P)\,Y_\varepsilon(r) \\
&\quad \times \sum_{k=0}^{\omega(P)} (-1)^k
  \sum_{\substack{d \in P.\text{divisors} \\ \omega(d) = k}}
    d^{-\varepsilon}\,\operatorname{Re} S_r\bigl(\lfloor N / d \rfloor\bigr).
\end{aligned}
$$ -/
theorem all_depth_coherent_pmRamanujanEnergyCenteredPrimitive_eq {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hr : 1 < r) (hPr : Nat.Coprime P r) (N : ℕ) :
    (∑ m ∈ P.divisors,
        pmRealRamanujanWeight ε (m * r) * pmRamanujanEnergyCenteredPrimitive (m * r) N) =
      pmRealRamanujanWeight ε r * vonMangoldt r +
        pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r *
          ∑ k ∈ Finset.range (cardDistinctFactors P + 1),
            (-1 : ℝ) ^ k *
              ∑ d ∈ P.divisors.filter (fun d => cardDistinctFactors d = k),
                (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re := by
  have hec_split :
      (∑ m ∈ P.divisors,
          pmRealRamanujanWeight ε (m * r) * pmRamanujanEnergyCenteredPrimitive (m * r) N) =
        (∑ m ∈ P.divisors,
          pmRealRamanujanWeight ε (m * r) * (pmRamanujanPrimitive (m * r) N).re) +
        (∑ m ∈ P.divisors,
          pmRealRamanujanWeight ε (m * r) * vonMangoldt (m * r)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold pmRamanujanEnergyCenteredPrimitive
    ring
  have hΛ_sum :
      (∑ m ∈ P.divisors, pmRealRamanujanWeight ε (m * r) * vonMangoldt (m * r)) =
        pmRealRamanujanWeight ε r * vonMangoldt r := by
    have h1 : 1 ∈ P.divisors := Nat.one_mem_divisors.mpr hP.ne_zero
    rw [← Finset.add_sum_erase _ _ h1, one_mul]
    suffices hzero :
        ∑ m ∈ P.divisors.erase 1, pmRealRamanujanWeight ε (m * r) * vonMangoldt (m * r) = 0 by
      rw [hzero, add_zero]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_erase] at hm
    have hm_pos : 0 < m := Nat.pos_of_mem_divisors hm.2
    have hm_gt : 1 < m := Nat.lt_of_le_of_ne hm_pos (Ne.symm hm.1)
    have hcop_mr : Nat.Coprime m r := hPr.coprime_dvd_left (Nat.dvd_of_mem_divisors hm.2)
    rw [vonMangoldt_mul_eq_zero_of_coprime hcop_mr hm_gt hr, mul_zero]
  have hprim := all_depth_coherent_pmRamanujanPrimitive_eq hε hP hPr N
  have hshell :=
    sum_divisors_moebiusReal_eq_alternating_depth_shells hP
      (fun d => (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re)
  have hprim' :
      (∑ m ∈ P.divisors,
          pmRealRamanujanWeight ε (m * r) * (pmRamanujanPrimitive (m * r) N).re) =
        pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r *
          ∑ k ∈ Finset.range (cardDistinctFactors P + 1),
            (-1 : ℝ) ^ k *
              ∑ d ∈ P.divisors.filter (fun d => cardDistinctFactors d = k),
                (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re := by
    rw [hprim, ← hshell]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  linarith

end GaloisForLFunctions.BezoutValuationIncidence

