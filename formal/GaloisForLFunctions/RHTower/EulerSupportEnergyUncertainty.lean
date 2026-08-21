import GaloisForLFunctions.RHTower.RelativeStripDivisorReflection

/-!
# Euler support-energy-position uncertainty

Weighted Hoelder on the prime-power index set converts an `l^q` bound on the logarithmic Euler
discrepancy and a convergence exponent for its prime support into an absolute-convergence
abscissa for the discrepancy series:

```text
sigma_E <= sigma_q + delta/q'.
```

Combined with the relative-strip reflection theorem this is a position constraint: a
reflection-stable divisor point at horizontal distance `a` from the critical line forces
`sigma_q + delta/q' >= 1/2 + a`.

The tempered strengthening is the observation that with uniformly bounded prime-power traces the
deep prime powers `k >= 2` already converge on `Re s > 1/2`, so only the prime traces can obstruct
the critical line.
-/

open scoped NNReal

namespace RHTower

noncomputable section

variable {ι : Type*}

/-! ## Weighted Hölder for summable families -/

/-- Hölder's inequality makes the product of an `ℓ^p` and an `ℓ^q` nonnegative family summable. -/
theorem summable_mul_of_rpow_summable {f g : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hfs : Summable fun i => f i ^ p) (hgs : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i := by
  set F : ι → ℝ≥0 := fun i => ⟨f i, hf i⟩ with hF
  set G : ι → ℝ≥0 := fun i => ⟨g i, hg i⟩ with hG
  have hFs : Summable fun i => F i ^ p := by
    rw [← NNReal.summable_coe]
    refine hfs.congr fun i => ?_
    rw [NNReal.coe_rpow]
    rfl
  have hGs : Summable fun i => G i ^ q := by
    rw [← NNReal.summable_coe]
    refine hgs.congr fun i => ?_
    rw [NNReal.coe_rpow]
    rfl
  have hmul := (NNReal.summable_and_inner_le_Lp_mul_Lq_tsum hpq hFs hGs).1
  rw [← NNReal.summable_coe] at hmul
  refine hmul.congr fun i => ?_
  rw [NNReal.coe_mul]
  rfl

/-! ## The weighted Hölder abscissa bound -/

/-- **Weighted Hölder abscissa bound `(H)`.**  If the weighted `ℓ^q` energy of the discrepancy
converges at abscissa `v` and the weighted support series converges at abscissa `q' * w`, then the
absolute discrepancy series converges at abscissa `v + w`. -/
theorem summable_absDiscrepancy_of_holder {a : ι → ℂ} {mu wt : ι → ℝ}
    (hwt : ∀ i, 0 ≤ wt i) {q q' v w : ℝ} (hqq' : q.HolderConjugate q')
    (hE : Summable fun i => ‖a i‖ ^ q * Real.exp (-(mu i) * (q * v)) * wt i)
    (hS : Summable fun i => Real.exp (-(mu i) * (q' * w)) * wt i) :
    Summable fun i => (‖a i‖ * wt i) * Real.exp (-(mu i) * (v + w)) := by
  have hq : 0 < q := hqq'.pos
  have hq' : 0 < q' := hqq'.symm.pos
  have hinv : q⁻¹ + q'⁻¹ = 1 := by simpa using hqq'.inv_add_inv_eq_inv
  set f : ι → ℝ := fun i => ‖a i‖ * Real.exp (-(mu i) * v) * wt i ^ (1 / q) with hf
  set g : ι → ℝ := fun i => Real.exp (-(mu i) * w) * wt i ^ (1 / q') with hg
  have hfnn : ∀ i, 0 ≤ f i := by
    intro i
    have := hwt i
    positivity
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i
    have := hwt i
    positivity
  have hfq : ∀ i, f i ^ q = ‖a i‖ ^ q * Real.exp (-(mu i) * (q * v)) * wt i := by
    intro i
    have hwti := hwt i
    rw [hf]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    · congr 1
      rw [← Real.exp_mul]
      ring_nf
    · rw [← Real.rpow_mul hwti, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
  have hgq : ∀ i, g i ^ q' = Real.exp (-(mu i) * (q' * w)) * wt i := by
    intro i
    have hwti := hwt i
    rw [hg, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    · rw [← Real.exp_mul]
      ring_nf
    · rw [← Real.rpow_mul hwti, one_div, inv_mul_cancel₀ hq'.ne', Real.rpow_one]
  have hprod : ∀ i, f i * g i = (‖a i‖ * wt i) * Real.exp (-(mu i) * (v + w)) := by
    intro i
    have hwti := hwt i
    have hw : wt i ^ (1 / q) * wt i ^ (1 / q') = wt i := by
      rw [← Real.rpow_add' hwti (by rw [one_div, one_div, hinv]; norm_num),
        one_div, one_div, hinv, Real.rpow_one]
    rw [hf, hg]
    calc ‖a i‖ * Real.exp (-(mu i) * v) * wt i ^ (1 / q) *
          (Real.exp (-(mu i) * w) * wt i ^ (1 / q'))
        = ‖a i‖ * (Real.exp (-(mu i) * v) * Real.exp (-(mu i) * w)) *
            (wt i ^ (1 / q) * wt i ^ (1 / q')) := by ring
      _ = (‖a i‖ * wt i) * Real.exp (-(mu i) * (v + w)) := by
          rw [← Real.exp_add, hw]
          ring_nf
  have hsum := summable_mul_of_rpow_summable hfnn hgnn hqq'
    (by simpa only [hfq] using hE) (by simpa only [hgq] using hS)
  exact hsum.congr hprod

/-! ## The prime-power index -/

variable {S : Set Nat.Primes}

/-- The natural number carried by a prime-power index `(p, k)`, namely `p ^ (k + 1)`. -/
def primePowerNat (z : S × ℕ) : ℕ := (z.1.1.1) ^ (z.2 + 1)

/-- The prime-power frequency `μ(p, k) = (k + 1) log p`. -/
def primePowerMu (z : S × ℕ) : ℝ := ((z.2 : ℝ) + 1) * Real.log (z.1.1.1 : ℕ)

/-- The harmonic weight `1 / (k + 1)` of a prime power. -/
def primePowerWeight (z : S × ℕ) : ℝ := 1 / ((z.2 : ℝ) + 1)

theorem two_le_primeCoe (z : S × ℕ) : (2 : ℝ) ≤ (z.1.1.1 : ℕ) := by
  exact_mod_cast z.1.1.2.two_le

theorem primePowerMu_nonneg (z : S × ℕ) : 0 ≤ primePowerMu z := by
  have h2 := two_le_primeCoe z
  have : (0 : ℝ) ≤ Real.log (z.1.1.1 : ℕ) := Real.log_nonneg (by linarith)
  have hk : (0 : ℝ) ≤ (z.2 : ℝ) + 1 := by positivity
  exact mul_nonneg hk this

theorem primePowerWeight_nonneg (z : S × ℕ) : 0 ≤ primePowerWeight z := by
  unfold primePowerWeight
  positivity

theorem primePowerWeight_le_one (z : S × ℕ) : primePowerWeight z ≤ 1 := by
  unfold primePowerWeight
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ (z.2 : ℝ) := Nat.cast_nonneg _
  linarith

theorem exp_primePowerMu (z : S × ℕ) (σ : ℝ) :
    Real.exp (-(primePowerMu z) * σ) = ((z.1.1.1 : ℕ) : ℝ) ^ (-(((z.2 : ℝ) + 1) * σ)) := by
  have hp : (0 : ℝ) < ((z.1.1.1 : ℕ) : ℝ) := by
    have := two_le_primeCoe z
    linarith
  rw [Real.rpow_def_of_pos hp, primePowerMu]
  congr 1
  ring

/-- **The harmonic prime-power support series is dominated by the prime series.**  For a positive
exponent, `∑_{p ∈ S} ∑_{k ≥ 1} p^{-k u} / k` converges as soon as `∑_{p ∈ S} p^{-u}` does. -/
theorem summable_primePowerSupport {u : ℝ} (hu : 0 < u)
    (hS : Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-u)) :
    Summable fun z : S × ℕ => Real.exp (-(primePowerMu z) * u) * primePowerWeight z := by
  have hhalf : (2 : ℝ) ^ (-u) < 1 := by
    calc (2 : ℝ) ^ (-u) < (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero _
  have hhalfnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-u) := Real.rpow_nonneg (by norm_num) _
  set C : ℝ := (1 - (2 : ℝ) ^ (-u))⁻¹ with hC
  have hCpos : 0 < C := by
    rw [hC, inv_pos]
    linarith
  have hterm : ∀ z : S × ℕ, 0 ≤ Real.exp (-(primePowerMu z) * u) * primePowerWeight z := fun z =>
    mul_nonneg (Real.exp_nonneg _) (primePowerWeight_nonneg z)
  have hpbound : ∀ (p : S) (k : ℕ),
      Real.exp (-(primePowerMu ((p, k) : S × ℕ)) * u) * primePowerWeight ((p, k) : S × ℕ)
        ≤ ((p.1.1 : ℕ) : ℝ) ^ (-u) * ((2 : ℝ) ^ (-u)) ^ k := by
    intro p k
    have hp2 : (2 : ℝ) ≤ ((p.1.1 : ℕ) : ℝ) := two_le_primeCoe ((p, 0) : S × ℕ)
    have hp0 : (0 : ℝ) < ((p.1.1 : ℕ) : ℝ) := by linarith
    have hexp : Real.exp (-(primePowerMu ((p, k) : S × ℕ)) * u)
        = ((p.1.1 : ℕ) : ℝ) ^ (-(((k : ℝ) + 1) * u)) := exp_primePowerMu _ _
    have hsplit : ((p.1.1 : ℕ) : ℝ) ^ (-(((k : ℝ) + 1) * u))
        = ((p.1.1 : ℕ) : ℝ) ^ (-u) * ((p.1.1 : ℕ) : ℝ) ^ (-((k : ℝ) * u)) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have hbase : ((p.1.1 : ℕ) : ℝ) ^ (-((k : ℝ) * u)) ≤ (2 : ℝ) ^ (-((k : ℝ) * u)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      refine inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _) ?_
      exact Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    have hpow : (2 : ℝ) ^ (-((k : ℝ) * u)) = ((2 : ℝ) ^ (-u)) ^ k := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-u)) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    calc Real.exp (-(primePowerMu ((p, k) : S × ℕ)) * u) * primePowerWeight ((p, k) : S × ℕ)
        ≤ Real.exp (-(primePowerMu ((p, k) : S × ℕ)) * u) * 1 :=
          mul_le_mul_of_nonneg_left (primePowerWeight_le_one _) (Real.exp_nonneg _)
      _ = ((p.1.1 : ℕ) : ℝ) ^ (-u) * ((p.1.1 : ℕ) : ℝ) ^ (-((k : ℝ) * u)) := by
          rw [mul_one, hexp, hsplit]
      _ ≤ ((p.1.1 : ℕ) : ℝ) ^ (-u) * (2 : ℝ) ^ (-((k : ℝ) * u)) :=
          mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hp0.le _)
      _ = ((p.1.1 : ℕ) : ℝ) ^ (-u) * ((2 : ℝ) ^ (-u)) ^ k := by rw [hpow]
  have hgeoSummable : Summable fun k : ℕ => ((2 : ℝ) ^ (-u)) ^ k :=
    summable_geometric_of_lt_one hhalfnn hhalf
  have hinner : ∀ p : S, Summable fun k : ℕ =>
      Real.exp (-(primePowerMu ((p, k) : S × ℕ)) * u) * primePowerWeight ((p, k) : S × ℕ) := by
    intro p
    exact Summable.of_nonneg_of_le (fun k => hterm _) (hpbound p)
      (hgeoSummable.mul_left (((p.1.1 : ℕ) : ℝ) ^ (-u)))
  have houter : Summable fun p : S => ∑' k : ℕ,
      Real.exp (-(primePowerMu ((p, k) : S × ℕ)) * u) * primePowerWeight ((p, k) : S × ℕ) := by
    refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun k => hterm _) (fun p => ?_)
      (hS.mul_left C)
    calc (∑' k : ℕ, Real.exp (-(primePowerMu ((p, k) : S × ℕ)) * u) *
            primePowerWeight ((p, k) : S × ℕ))
        ≤ ∑' k : ℕ, ((p.1.1 : ℕ) : ℝ) ^ (-u) * ((2 : ℝ) ^ (-u)) ^ k :=
          (hinner p).tsum_le_tsum (hpbound p) (hgeoSummable.mul_left _)
      _ = ((p.1.1 : ℕ) : ℝ) ^ (-u) * C := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hhalfnn hhalf, hC]
      _ = C * ((p.1.1 : ℕ) : ℝ) ^ (-u) := mul_comm _ _
  exact (summable_prod_of_nonneg hterm).mpr ⟨hinner, houter⟩

/-! ## The Euler discrepancy series and its Hölder abscissa -/

/-- The logarithmic Euler discrepancy series `∑_{p,k} c(p,k) p^{-ks} / k`. -/
def eulerDiscrepancySeries (c : S × ℕ → ℂ) : ℂ → ℂ :=
  dirichletSeries (fun z => c z * (primePowerWeight z : ℂ)) primePowerMu

theorem norm_eulerDiscrepancyCoeff (c : S × ℕ → ℂ) (z : S × ℕ) :
    ‖c z * (primePowerWeight z : ℂ)‖ = ‖c z‖ * primePowerWeight z := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (primePowerWeight_nonneg z)]

/-- **`(H)` at one pair of exponents.**  The weighted `ℓ^q` energy at `v` and the prime support
series at `q' * w` force absolute convergence of the discrepancy series at `v + w`. -/
theorem summable_eulerDiscrepancy_of_holder {c : S × ℕ → ℂ} {q q' v w : ℝ}
    (hqq' : q.HolderConjugate q') (hw : 0 < q' * w)
    (hE : Summable fun z : S × ℕ =>
      ‖c z‖ ^ q * Real.exp (-(primePowerMu z) * (q * v)) * primePowerWeight z)
    (hSupp : Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-(q' * w))) :
    Summable fun z : S × ℕ =>
      ‖c z * (primePowerWeight z : ℂ)‖ * Real.exp (-(primePowerMu z) * (v + w)) := by
  simp only [norm_eulerDiscrepancyCoeff]
  exact summable_absDiscrepancy_of_holder primePowerWeight_nonneg hqq' hE
    (summable_primePowerSupport hw hSupp)

/-- **`(H)` in abscissa form.**  If the weighted `ℓ^q` energy converges strictly to the right of
`σ_q` and the prime support series strictly to the right of `δ`, then the absolute discrepancy
series converges strictly to the right of `σ_q + δ/q'`. -/
theorem summable_eulerDiscrepancy_abscissa {c : S × ℕ → ℂ} {q q' sigmaq delta : ℝ}
    (hqq' : q.HolderConjugate q') (hdelta : 0 ≤ delta)
    (hE : ∀ v : ℝ, sigmaq < v → Summable fun z : S × ℕ =>
      ‖c z‖ ^ q * Real.exp (-(primePowerMu z) * (q * v)) * primePowerWeight z)
    (hSupp : ∀ u : ℝ, delta < u → Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-u))
    {sigma : ℝ} (hsigma : sigmaq + delta / q' < sigma) :
    Summable fun z : S × ℕ =>
      ‖c z * (primePowerWeight z : ℂ)‖ * Real.exp (-(primePowerMu z) * sigma) := by
  have hq' : 0 < q' := hqq'.symm.pos
  set eps : ℝ := sigma - (sigmaq + delta / q') with heps
  have hepspos : 0 < eps := by rw [heps]; linarith
  set v : ℝ := sigmaq + eps / 2 with hv
  set w : ℝ := delta / q' + eps / 2 with hw
  have hvw : v + w = sigma := by rw [hv, hw, heps]; ring
  have hqw : delta < q' * w := by
    rw [hw, mul_add, mul_div_cancel₀ _ hq'.ne']
    have : 0 < q' * (eps / 2) := by positivity
    linarith
  have hwpos : 0 < q' * w := lt_of_le_of_lt hdelta hqw
  have := summable_eulerDiscrepancy_of_holder hqq' hwpos
    (hE v (by rw [hv]; linarith)) (hSupp (q' * w) hqw)
  rwa [hvw] at this

/-! ## The divisor consequence -/

/-- **`(P)` and `(U)`.**  A reflection-stable divisor confined to `Re s ≤ A` has transverse radius
at most `A - 1/2`; equivalently a divisor point at horizontal distance `a` forces `1/2 + a ≤ A`. -/
theorem holderBudget_ge_of_divisorPoint {D : Set ℂ} {A : ℝ}
    (hright : ∀ ρ ∈ D, ρ.re ≤ A) (hrefl : ∀ ρ ∈ D, (1 - ρ) ∈ D) {ρ : ℂ} (hρ : ρ ∈ D) :
    1 / 2 + |ρ.re - 1 / 2| ≤ A := by
  have := abs_re_sub_half_le_of_reflection hright hrefl hρ
  linarith

/-! ## The tempered split -/

theorem summable_primeRpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => ((p.1 : ℕ) : ℝ) ^ (-σ) := by
  have hnat : Summable fun n : ℕ => ((n : ℝ)) ^ (-σ) := by
    simpa using Real.summable_nat_rpow_inv.mpr hσ
  exact hnat.comp_injective (fun p q h => Subtype.ext (by exact_mod_cast h))

/-- The deep prime powers `k ≥ 2` are dominated by the square of the prime series. -/
theorem summable_primePowerSupport_deep {u : ℝ} (hu : 0 < u)
    (hS : Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u))) :
    Summable fun z : S × ℕ =>
      Real.exp (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * u) *
        primePowerWeight ((z.1, z.2 + 1) : S × ℕ) := by
  have hhalf : (2 : ℝ) ^ (-u) < 1 := by
    calc (2 : ℝ) ^ (-u) < (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero _
  have hhalfnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-u) := Real.rpow_nonneg (by norm_num) _
  set C : ℝ := (1 - (2 : ℝ) ^ (-u))⁻¹ with hC
  have hCpos : 0 < C := by
    rw [hC, inv_pos]; linarith
  have hterm : ∀ z : S × ℕ,
      0 ≤ Real.exp (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * u) *
        primePowerWeight ((z.1, z.2 + 1) : S × ℕ) := fun z =>
    mul_nonneg (Real.exp_nonneg _) (primePowerWeight_nonneg _)
  have hpbound : ∀ (p : S) (j : ℕ),
      Real.exp (-(primePowerMu ((p, j + 1) : S × ℕ)) * u) *
          primePowerWeight ((p, j + 1) : S × ℕ)
        ≤ ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) * ((2 : ℝ) ^ (-u)) ^ j := by
    intro p j
    have hp2 : (2 : ℝ) ≤ ((p.1.1 : ℕ) : ℝ) := two_le_primeCoe ((p, 0) : S × ℕ)
    have hp0 : (0 : ℝ) < ((p.1.1 : ℕ) : ℝ) := by linarith
    have hexp : Real.exp (-(primePowerMu ((p, j + 1) : S × ℕ)) * u)
        = ((p.1.1 : ℕ) : ℝ) ^ (-((((j : ℕ) + 1 : ℕ) : ℝ) + 1) * u) := by
      have := exp_primePowerMu ((p, j + 1) : S × ℕ) u
      rw [this]
      congr 1
      ring
    have hsplit : ((p.1.1 : ℕ) : ℝ) ^ (-((((j : ℕ) + 1 : ℕ) : ℝ) + 1) * u)
        = ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) * ((p.1.1 : ℕ) : ℝ) ^ (-((j : ℝ) * u)) := by
      rw [← Real.rpow_add hp0]
      congr 1
      push_cast
      ring
    have hbase : ((p.1.1 : ℕ) : ℝ) ^ (-((j : ℝ) * u)) ≤ (2 : ℝ) ^ (-((j : ℝ) * u)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      refine inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _) ?_
      exact Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    have hpow : (2 : ℝ) ^ (-((j : ℝ) * u)) = ((2 : ℝ) ^ (-u)) ^ j := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-u)) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    calc Real.exp (-(primePowerMu ((p, j + 1) : S × ℕ)) * u) *
            primePowerWeight ((p, j + 1) : S × ℕ)
        ≤ Real.exp (-(primePowerMu ((p, j + 1) : S × ℕ)) * u) * 1 :=
          mul_le_mul_of_nonneg_left (primePowerWeight_le_one _) (Real.exp_nonneg _)
      _ = ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) * ((p.1.1 : ℕ) : ℝ) ^ (-((j : ℝ) * u)) := by
          rw [mul_one, hexp, hsplit]
      _ ≤ ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) * (2 : ℝ) ^ (-((j : ℝ) * u)) :=
          mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hp0.le _)
      _ = ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) * ((2 : ℝ) ^ (-u)) ^ j := by rw [hpow]
  have hgeoSummable : Summable fun j : ℕ => ((2 : ℝ) ^ (-u)) ^ j :=
    summable_geometric_of_lt_one hhalfnn hhalf
  have hinner : ∀ p : S, Summable fun j : ℕ =>
      Real.exp (-(primePowerMu ((p, j + 1) : S × ℕ)) * u) *
        primePowerWeight ((p, j + 1) : S × ℕ) := fun p =>
    Summable.of_nonneg_of_le (fun j => hterm (p, j)) (hpbound p)
      (hgeoSummable.mul_left (((p.1.1 : ℕ) : ℝ) ^ (-(2 * u))))
  have houter : Summable fun p : S => ∑' j : ℕ,
      Real.exp (-(primePowerMu ((p, j + 1) : S × ℕ)) * u) *
        primePowerWeight ((p, j + 1) : S × ℕ) := by
    refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun j => hterm (p, j)) (fun p => ?_)
      (hS.mul_left C)
    calc (∑' j : ℕ, Real.exp (-(primePowerMu ((p, j + 1) : S × ℕ)) * u) *
            primePowerWeight ((p, j + 1) : S × ℕ))
        ≤ ∑' j : ℕ, ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) * ((2 : ℝ) ^ (-u)) ^ j :=
          (hinner p).tsum_le_tsum (hpbound p) (hgeoSummable.mul_left _)
      _ = ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) * C := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hhalfnn hhalf, hC]
      _ = C * ((p.1.1 : ℕ) : ℝ) ^ (-(2 * u)) := mul_comm _ _
  exact (summable_prod_of_nonneg hterm).mpr ⟨hinner, houter⟩

/-- **`(2)`.**  With uniformly bounded prime-power traces the deep prime powers `k ≥ 2` converge on
`Re s > 1/2`, so they never obstruct the critical line. -/
theorem summable_highPrimePower_of_bounded {c : S × ℕ → ℂ} {B : ℝ}
    (hB : ∀ z : S × ℕ, ‖c z‖ ≤ B) {σ : ℝ} (hσ : 1 / 2 < σ)
    (hSupp : Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-(2 * σ))) :
    Summable fun z : S × ℕ =>
      ‖c ((z.1, z.2 + 1) : S × ℕ) * (primePowerWeight ((z.1, z.2 + 1) : S × ℕ) : ℂ)‖ *
        Real.exp (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * σ) := by
  have hσ0 : 0 < σ := by linarith
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((summable_primePowerSupport_deep hσ0 hSupp).mul_left B)
  rw [norm_eulerDiscrepancyCoeff]
  calc ‖c ((z.1, z.2 + 1) : S × ℕ)‖ * primePowerWeight ((z.1, z.2 + 1) : S × ℕ) *
        Real.exp (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * σ)
      ≤ B * primePowerWeight ((z.1, z.2 + 1) : S × ℕ) *
          Real.exp (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * σ) := by
        have h2 := primePowerWeight_nonneg ((z.1, z.2 + 1) : S × ℕ)
        have h3 := Real.exp_nonneg (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * σ)
        gcongr
        exact hB _
    _ = B * (Real.exp (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * σ) *
          primePowerWeight ((z.1, z.2 + 1) : S × ℕ)) := by ring

/-! ## The square-energy law and the capstone -/

theorem holderConjugate_two : (2 : ℝ).HolderConjugate 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **`(4)`  The square-energy law.**  At `q = 2` the Hölder budget is `σ₂ + δ/2`. -/
theorem summable_eulerDiscrepancy_squareEnergy {c : S × ℕ → ℂ} {sigma2 delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hE : ∀ v : ℝ, sigma2 < v → Summable fun z : S × ℕ =>
      ‖c z‖ ^ (2 : ℝ) * Real.exp (-(primePowerMu z) * (2 * v)) * primePowerWeight z)
    (hSupp : ∀ u : ℝ, delta < u → Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-u))
    {sigma : ℝ} (hsigma : sigma2 + delta / 2 < sigma) :
    Summable fun z : S × ℕ =>
      ‖c z * (primePowerWeight z : ℂ)‖ * Real.exp (-(primePowerMu z) * sigma) :=
  summable_eulerDiscrepancy_abscissa holderConjugate_two hdelta hE hSupp hsigma

/-- **Euler support–energy–position uncertainty.**  The weighted Hölder abscissa bound `(H)`, the
tempered deep-prime-power estimate `(2)`, and the position inequality `(P)`. -/
theorem euler_support_energy_position_uncertainty :
    (∀ {S : Set Nat.Primes} {c : S × ℕ → ℂ} {q q' sigmaq delta : ℝ},
        q.HolderConjugate q' → 0 ≤ delta →
        (∀ v : ℝ, sigmaq < v → Summable fun z : S × ℕ =>
          ‖c z‖ ^ q * Real.exp (-(primePowerMu z) * (q * v)) * primePowerWeight z) →
        (∀ u : ℝ, delta < u → Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-u)) →
        ∀ {sigma : ℝ}, sigmaq + delta / q' < sigma →
          Summable fun z : S × ℕ =>
            ‖c z * (primePowerWeight z : ℂ)‖ * Real.exp (-(primePowerMu z) * sigma)) ∧
      (∀ {S : Set Nat.Primes} {c : S × ℕ → ℂ} {B : ℝ}, (∀ z : S × ℕ, ‖c z‖ ≤ B) →
        ∀ {sigma : ℝ}, 1 / 2 < sigma →
        (Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-(2 * sigma))) →
          Summable fun z : S × ℕ =>
            ‖c ((z.1, z.2 + 1) : S × ℕ) * (primePowerWeight ((z.1, z.2 + 1) : S × ℕ) : ℂ)‖ *
              Real.exp (-(primePowerMu ((z.1, z.2 + 1) : S × ℕ)) * sigma)) ∧
      (∀ {D : Set ℂ} {A : ℝ}, (∀ ρ ∈ D, ρ.re ≤ A) → (∀ ρ ∈ D, (1 - ρ) ∈ D) →
        ∀ {ρ : ℂ}, ρ ∈ D → 1 / 2 + |ρ.re - 1 / 2| ≤ A) :=
  by
  refine ⟨?_, ?_, ?_⟩
  · intro S c q q' sigmaq delta hqq' hdelta hE hSupp sigma hsigma
    exact summable_eulerDiscrepancy_abscissa hqq' hdelta hE hSupp hsigma
  · intro S c B hB sigma hsigma hSupp
    exact summable_highPrimePower_of_bounded hB hsigma hSupp
  · intro D A hright hrefl ρ hρ
    exact holderBudget_ge_of_divisorPoint hright hrefl hρ

end

end RHTower
