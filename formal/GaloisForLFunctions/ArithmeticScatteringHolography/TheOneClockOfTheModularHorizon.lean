import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinWavePacket
import GaloisForLFunctions.RHTower.EisensteinHeckeOperator

/-!
# The one clock of the modular horizon

The bulk of the modular horizon is adelic: `Γ\(ℍ × Π_p T_p)`, where the Hecke operator `T_p` is the adjacency of the
tree at `p`. One could expect independent dynamics at each place. On the Eisenstein sector there is only one
clock.

* **Hecke is a wave propagator.** For a prime `p`, the Eisenstein function is an eigenfunction with eigenvalue
  `p^u + p^{-u}` (`heckeOp_normalizedEisenstein`). So on a wave packet,

  `T_p 𝓕(τ) = 𝓕(τ + log p) + 𝓕(τ - log p)`

  (`heckeOp_wavePacket`): the normalized Hecke operator at `p` is translation of modular time by `±log p`.
* **The packet solves the wave equation of every tree.** The rescaled packet `p^{n/2} 𝓕(τ + n log p)` solves the
  discrete wave equation of the `(p+1)`-regular tree with `n` as time (`treeWave_isWave`), and this holds at
  every prime with the same `𝓕`. The trees run on the modular clock, with tick `log p`.

So **Hecke at a second place is not an independent constraint on the flux through the first**: on the Eisenstein
sector it is a function of the wave group, and the same is proved on the graph (where `T_Q` acts as `A`
on the radial sector). The independent content of Hecke lies on the cuspidal sector, where the Hecke eigenvalue
is not a function of the Laplace eigenvalue, and that sector has no resonances.

* **Horocycle renormalization.** The mean over a closed horocycle obeys
  `H[T_p F](y) = p^{-½} H[F](p y) + p^{½} H[F](y/p)` (`horoMean_heckeOp`). For the packet this is the d'Alembert
  form of the constant term, and it is why the Hecke relation and the wave equation agree on the reflected
  signal.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

open GaloisForLFunctions.BlackHoleRingdown

/-- The prime `p` as a positive complex number has `p^{½+u} = √p · p^u`. -/
theorem cpow_half_add {p : ℕ} (hp : 0 < p) (u : ℂ) :
    (p : ℂ) ^ (1 / 2 + u) = (Real.sqrt p : ℂ) * (p : ℂ) ^ u := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_add _ _ hpC, RHTower.sqrt_eq_cpow_half]

theorem cpow_half_sub {p : ℕ} (hp : 0 < p) (u : ℂ) :
    (p : ℂ) ^ (1 / 2 - u) = (Real.sqrt p : ℂ) * ((p : ℂ) ^ u)⁻¹ := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hpC, RHTower.sqrt_eq_cpow_half, Complex.cpow_neg]

/-- **The Eisenstein function is a Hecke eigenfunction**, written with no junk at the poles. -/
theorem heckeOp_normalizedEisenstein {p : ℕ} (hp : p.Prime) (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    RHTower.heckeOp p (normalizedEisenstein u) x Y =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * normalizedEisenstein u x Y := by
  have hp0 : 0 < p := hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hr : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp0)
    exact_mod_cast this.ne'
  have hP : (p : ℂ) ^ u ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hpC h.1
  have hrr : (p : ℂ) = (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]
    exact (Complex.ofReal_natCast p).symm
  have hneg : (p : ℂ) ^ (-u) = ((p : ℂ) ^ u)⁻¹ := Complex.cpow_neg _ _
  have hfun : normalizedEisenstein u = fun x Y =>
      (fun _ (Y : ℝ) => (1 : ℂ) * (Y : ℂ) ^ (1 / 2 + u)) x Y +
        ((fun _ (Y : ℝ) => scatteringPhase u * (Y : ℂ) ^ (1 / 2 - u)) x Y +
          (fun x Y => tailWeight u * ((fun x Y => ∑' N : ℕ, RHTower.eisensteinTailTerm false x Y N u) x Y +
            (fun x Y => ∑' N : ℕ, RHTower.eisensteinTailTerm true x Y N u) x Y)) x Y) := by
    funext x Y
    unfold normalizedEisenstein eisTail
    rw [RHTower.weightedTail_eq_signedSqrtWhittakerTail,
      RHTower.weightedTail_eq_signedSqrtWhittakerTail,
      RHTower.signedSqrtWhittakerTail_eq_tsum_term, RHTower.signedSqrtWhittakerTail_eq_tsum_term]
    ring
  have hval : normalizedEisenstein u x Y = 1 * (Y : ℂ) ^ (1 / 2 + u) +
      (scatteringPhase u * (Y : ℂ) ^ (1 / 2 - u) + tailWeight u *
        ((∑' N : ℕ, RHTower.eisensteinTailTerm false x Y N u) +
          ∑' N : ℕ, RHTower.eisensteinTailTerm true x Y N u)) := congrFun (congrFun hfun x) Y
  rw [hval, hfun]
  rw [RHTower.heckeOp_add, RHTower.heckeOp_add, RHTower.heckeOp_cpow p 1 _ x hY,
    RHTower.heckeOp_cpow p _ _ x hY, RHTower.heckeOp_const_mul, RHTower.heckeOp_add,
    RHTower.heckeOp_tail false hp x hY, RHTower.heckeOp_tail true hp x hY]
  rw [cpow_half_add hp0, cpow_half_sub hp0, hneg]
  have e1 : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * ((Real.sqrt p : ℂ) * (p : ℂ) ^ u +
      (p : ℂ) * ((Real.sqrt p : ℂ) * (p : ℂ) ^ u)⁻¹) = (p : ℂ) ^ u + ((p : ℂ) ^ u)⁻¹ := by
    nth_rewrite 2 [hrr]
    push_cast
    exact RHTower.hecke_weyl_scalar_pos hr hP
  have e2 : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * ((Real.sqrt p : ℂ) * ((p : ℂ) ^ u)⁻¹ +
      (p : ℂ) * ((Real.sqrt p : ℂ) * ((p : ℂ) ^ u)⁻¹)⁻¹) = (p : ℂ) ^ u + ((p : ℂ) ^ u)⁻¹ := by
    nth_rewrite 2 [hrr]
    push_cast
    exact RHTower.hecke_weyl_scalar_neg hr hP
  rw [e1, e2]
  ring

variable {ε : ℝ}

/-- The integrability of the packet integrand at a point of the upper half-plane. -/
theorem integrable_packet_eisenstein (hε : 0 < ε) (ξ₀ τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Integrable fun ξ : ℝ => gaussianAmplitude ε ξ₀ (ξ : ℂ) *
      normalizedEisenstein ((ξ : ℂ) * I) x Y * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) :=
  (packetSymbol_eisenstein hε x hY).integrable hε ξ₀ τ

/-- **Hecke is a wave propagator.** On the Eisenstein wave packet, the normalized Hecke operator at `p` is
translation of modular time by `±log p`. -/
theorem heckeOp_wavePacket {p : ℕ} (hp : p.Prime) (hε : 0 < ε) (ξ₀ τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    RHTower.heckeOp p (wavePacket ε ξ₀ τ) x Y =
      wavePacket ε ξ₀ (τ + Real.log p) x Y + wavePacket ε ξ₀ (τ - Real.log p) x Y := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hYp : 0 < (p : ℝ) * Y := mul_pos hp0 hY
  have hYd : 0 < Y / (p : ℝ) := div_pos hY hp0
  have hI₁ := integrable_packet_eisenstein hε ξ₀ τ ((p : ℝ) * x) hYp
  have hI₂ : ∀ b ∈ Finset.range p, Integrable fun ξ : ℝ => gaussianAmplitude ε ξ₀ (ξ : ℂ) *
      normalizedEisenstein ((ξ : ℂ) * I) ((x + b) / p) (Y / p) *
        Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) :=
    fun b _ => integrable_packet_eisenstein hε ξ₀ τ _ hYd
  have hplus := integrable_packet_eisenstein hε ξ₀ (τ + Real.log p) x hY
  have hminus := integrable_packet_eisenstein hε ξ₀ (τ - Real.log p) x hY
  unfold RHTower.heckeOp
  simp only [wavePacket, packet]
  rw [← integral_finsetSum _ hI₂, ← integral_add hI₁ (integrable_finsetSum _ hI₂),
    ← integral_add hplus hminus, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have heig := heckeOp_normalizedEisenstein hp ((ξ : ℂ) * I) x hY
  unfold RHTower.heckeOp at heig
  have hpow : (p : ℂ) ^ ((ξ : ℂ) * I) = Complex.exp (I * (ξ : ℂ) * (Real.log p : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hpC, Complex.natCast_log]
    congr 1
    ring
  have hpowneg : (p : ℂ) ^ (-((ξ : ℂ) * I)) = Complex.exp (-(I * (ξ : ℂ) * (Real.log p : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero hpC, Complex.natCast_log]
    congr 1
    ring
  rw [hpow, hpowneg] at heig
  have eplus : Complex.exp (I * (ξ : ℂ) * ((τ + Real.log p : ℝ) : ℂ)) =
      Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) * Complex.exp (I * (ξ : ℂ) * (Real.log p : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have eminus : Complex.exp (I * (ξ : ℂ) * ((τ - Real.log p : ℝ) : ℂ)) =
      Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) * Complex.exp (-(I * (ξ : ℂ) * (Real.log p : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [eplus, eminus]
  have hexpand : gaussianAmplitude ε ξ₀ (ξ : ℂ) *
        normalizedEisenstein ((ξ : ℂ) * I) ((p : ℝ) * x) ((p : ℝ) * Y) *
          Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) +
      ∑ b ∈ Finset.range p, gaussianAmplitude ε ξ₀ (ξ : ℂ) *
        normalizedEisenstein ((ξ : ℂ) * I) ((x + b) / p) (Y / p) *
          Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) =
      gaussianAmplitude ε ξ₀ (ξ : ℂ) * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) *
        (normalizedEisenstein ((ξ : ℂ) * I) ((p : ℝ) * x) ((p : ℝ) * Y) +
          ∑ b ∈ Finset.range p, normalizedEisenstein ((ξ : ℂ) * I) ((x + b) / p) (Y / p)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      ring
  rw [hexpand]
  linear_combination
    (gaussianAmplitude ε ξ₀ (ξ : ℂ) * Complex.exp (I * (ξ : ℂ) * (τ : ℂ))) * heig

/-! ### Trees -/

/-- The packet seen from the tree at `p`: at tree time `n`, it is `𝓕` at modular time `τ + n log p`, weighted by
`p^{n/2}`, the energy normalization of the tree. -/
def treeWave (p : ℕ) (ε ξ₀ τ : ℝ) (n : ℤ) (x Y : ℝ) : ℂ :=
  (Real.sqrt p : ℂ) ^ n * wavePacket ε ξ₀ (τ + n * Real.log p) x Y

/-- **The packet solves the wave equation of the tree at `p`**, in the unnormalized Hecke operator
`√p T_p`, the adjacency of the `(p+1)`-regular tree. This holds for every prime with the same packet. -/
theorem treeWave_isWave {p : ℕ} (hp : p.Prime) (hε : 0 < ε) (ξ₀ τ : ℝ) (n : ℤ) (x : ℝ) {Y : ℝ}
    (hY : 0 < Y) :
    treeWave p ε ξ₀ τ (n + 1) x Y + (p : ℂ) * treeWave p ε ξ₀ τ (n - 1) x Y =
      (Real.sqrt p : ℂ) * RHTower.heckeOp p (treeWave p ε ξ₀ τ n) x Y := by
  have hp0 : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hr : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hrr : (p : ℂ) = (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]
    exact (Complex.ofReal_natCast p).symm
  have hfun : treeWave p ε ξ₀ τ n = fun x Y =>
      (Real.sqrt p : ℂ) ^ n * wavePacket ε ξ₀ (τ + n * Real.log p) x Y := rfl
  rw [hfun, RHTower.heckeOp_const_mul, heckeOp_wavePacket hp hε ξ₀ _ x hY]
  unfold treeWave
  have e1 : τ + ((n + 1 : ℤ) : ℝ) * Real.log p = τ + n * Real.log p + Real.log p := by
    push_cast
    ring
  have e2 : τ + ((n - 1 : ℤ) : ℝ) * Real.log p = τ + n * Real.log p - Real.log p := by
    push_cast
    ring
  rw [e1, e2, zpow_add₀ hr, zpow_sub₀ hr, zpow_one, hrr]
  field_simp

/-- **Two primes run on the same clock.** The Hecke operators at two primes compose to translations of the
modular time. -/
theorem heckeOp_heckeOp_wavePacket {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hε : 0 < ε) (ξ₀ τ x : ℝ) {Y : ℝ}
    (hY : 0 < Y) :
    RHTower.heckeOp p (fun x Y => RHTower.heckeOp r (wavePacket ε ξ₀ τ) x Y) x Y =
      wavePacket ε ξ₀ (τ + Real.log r + Real.log p) x Y +
        wavePacket ε ξ₀ (τ + Real.log r - Real.log p) x Y +
        (wavePacket ε ξ₀ (τ - Real.log r + Real.log p) x Y +
          wavePacket ε ξ₀ (τ - Real.log r - Real.log p) x Y) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have heq : RHTower.heckeOp p (fun x Y => RHTower.heckeOp r (wavePacket ε ξ₀ τ) x Y) x Y =
      RHTower.heckeOp p (fun x Y => wavePacket ε ξ₀ (τ + Real.log r) x Y +
        wavePacket ε ξ₀ (τ - Real.log r) x Y) x Y := by
    unfold RHTower.heckeOp
    congr 2
    · exact heckeOp_wavePacket hr hε ξ₀ τ _ (mul_pos hp0 hY)
    · refine Finset.sum_congr rfl fun b _ => ?_
      exact heckeOp_wavePacket hr hε ξ₀ τ _ (div_pos hY hp0)
  rw [heq, RHTower.heckeOp_add, heckeOp_wavePacket hp hε ξ₀ _ x hY,
    heckeOp_wavePacket hp hε ξ₀ _ x hY]

/-! ### The two branches on the horizon -/

/-- **The minus branch is outgoing on the modular horizon.** A resonant state has constant term `Y^{½ - p}`; with time
factor `e^{pτ}`, it is a function of `τ - log Y`. -/
theorem minusBranch_constantTerm (p : ℂ) (τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Complex.exp (p * τ) * (Y : ℂ) ^ (1 / 2 - p) =
      (Real.sqrt Y : ℂ) * Complex.exp (p * ((τ - Real.log Y : ℝ) : ℂ)) := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hsq : (Real.sqrt Y : ℂ) = (Y : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hY.le]
    push_cast
    ring_nf
  have hlog : Complex.log (Y : ℂ) = (Real.log Y : ℂ) := (Complex.ofReal_log hY.le).symm
  rw [hsq, sub_eq_add_neg, Complex.cpow_add _ _ hYC, Complex.cpow_def_of_ne_zero hYC (-p), hlog]
  have e : Complex.exp (p * ((τ - Real.log Y : ℝ) : ℂ)) =
      Complex.exp (p * τ) * Complex.exp ((Real.log Y : ℂ) * -p) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

/-- **The plus branch is incoming, so it is silent.** With time factor `e^{-pτ}` the same state is a function of
`τ + log Y`: the time reversal of the ringdown. -/
theorem plusBranch_constantTerm (p : ℂ) (τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Complex.exp (-p * τ) * (Y : ℂ) ^ (1 / 2 - p) =
      (Real.sqrt Y : ℂ) * Complex.exp (-p * ((τ + Real.log Y : ℝ) : ℂ)) := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hsq : (Real.sqrt Y : ℂ) = (Y : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hY.le]
    push_cast
    ring_nf
  have hlog : Complex.log (Y : ℂ) = (Real.log Y : ℂ) := (Complex.ofReal_log hY.le).symm
  rw [hsq, sub_eq_add_neg, Complex.cpow_add _ _ hYC, Complex.cpow_def_of_ne_zero hYC (-p), hlog]
  have e : Complex.exp (-p * ((τ + Real.log Y : ℝ) : ℂ)) =
      Complex.exp (-p * τ) * Complex.exp ((Real.log Y : ℂ) * -p) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

/-! ### Horocycle renormalization -/

/-- The mean of `F` over the closed horocycle at height `y`. -/
def horoMean (F : ℝ → ℝ → ℂ) (y : ℝ) : ℂ := ∫ x in (0 : ℝ)..1, F x y

/-- **Horocycle renormalization.** For `F` periodic in `x`, the mean of `T_p F` at height `y` is a combination of
the means at heights `p y` and `y/p`. -/
theorem horoMean_heckeOp {p : ℕ} (hp : 0 < p) {F : ℝ → ℝ → ℂ} (hper : ∀ x y, F (x + 1) y = F x y)
    (hcont : ∀ y, Continuous fun x => F x y) (y : ℝ) :
    horoMean (RHTower.heckeOp p F) y =
      ((Real.sqrt p)⁻¹ : ℝ) * horoMean F ((p : ℝ) * y) +
        ((Real.sqrt p : ℝ) : ℂ) * horoMean F (y / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    exact_mod_cast this.ne'
  have hrr : (p : ℂ) = (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]
    exact (Complex.ofReal_natCast p).symm
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  -- the first term: the horocycle wound `p` times
  have hfirst : ∫ x in (0 : ℝ)..1, F ((p : ℝ) * x) ((p : ℝ) * y) = horoMean F ((p : ℝ) * y) := by
    have hperF : Function.Periodic (fun x => F x ((p : ℝ) * y)) 1 := fun x => hper x _
    rw [intervalIntegral.integral_comp_mul_left (fun x => F x ((p : ℝ) * y)) hp0.ne']
    simp only [mul_zero, mul_one]
    have hsum := hperF.intervalIntegral_add_zsmul_eq (p : ℤ) 0
      (fun _ _ => (hcont _).intervalIntegrable _ _)
    simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at hsum
    rw [hsum]
    unfold horoMean
    simp only [Complex.real_smul]
    push_cast
    field_simp
  -- the second term: the horocycle cut into `p` arcs
  have hsecond : ∑ b ∈ Finset.range p, ∫ x in (0 : ℝ)..1, F ((x + b) / p) (y / p) =
      (p : ℂ) * horoMean F (y / p) := by
    have harc (b : ℕ) : ∫ x in (0 : ℝ)..1, F ((x + b) / p) (y / p) =
        (p : ℂ) * ∫ u in ((b : ℝ) / p)..(((b + 1 : ℕ) : ℝ) / p), F u (y / p) := by
      have e : (fun x : ℝ => F ((x + b) / p) (y / p)) =
          fun x => (fun u => F u (y / p)) ((p : ℝ)⁻¹ * x + (b : ℝ) / p) := by
        funext x
        congr 1
        field_simp
      rw [e, intervalIntegral.integral_comp_mul_add (fun u => F u (y / p)) (inv_ne_zero hp0.ne')]
      simp only [mul_zero, zero_add, mul_one, inv_inv, Complex.real_smul]
      push_cast
      congr 2
      field_simp
      ring
    simp only [harc]
    rw [← Finset.mul_sum]
    congr 1
    have hadj := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun u => F u (y / p)) (μ := volume) (a := fun b : ℕ => (b : ℝ) / p) (n := p)
      (fun k _ => (hcont _).intervalIntegrable _ _)
    have e0 : ((0 : ℕ) : ℝ) / p = 0 := by simp
    have e1 : ((p : ℕ) : ℝ) / p = 1 := div_self hp0.ne'
    rw [e0, e1] at hadj
    unfold horoMean
    rw [← hadj]
  have hint : ∀ b ∈ Finset.range p, IntervalIntegrable (fun x : ℝ => F ((x + b) / p) (y / p))
      volume 0 1 := by
    intro b _
    exact ((hcont _).comp ((continuous_id.add continuous_const).div_const _)).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun x : ℝ => F ((p : ℝ) * x) ((p : ℝ) * y)) volume 0 1 :=
    ((hcont _).comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => ∑ b ∈ Finset.range p, F ((x + b) / p) (y / p))
      volume 0 1 :=
    (continuous_finsetSum _ fun b _ =>
      (hcont _).comp ((continuous_id.add continuous_const).div_const _)).intervalIntegrable _ _
  unfold horoMean RHTower.heckeOp
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_finsetSum hint, hfirst, hsecond]
  unfold horoMean
  rw [hrr]
  push_cast
  field_simp

end GaloisForLFunctions.ArithmeticScatteringHolography

end
