import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DilationGibbsState

/-!
# Critical scaling of the clock overlap

The Gram kernel of the prime-gas heat vectors is zeta. Its pole gives a
half-plane Cauchy kernel at each clock center. Distinct fixed center times
have zero overlap in the scaling limit.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology
open _root_.RHTower.PrimeCoShift
open scoped ComplexConjugate

abbrev HeatVectorDomain := {s : ℂ // 1/2 < s.re}
abbrev PacketDirection := {z : ℂ // 0 < z.re}
abbrev PacketScale := {δ : ℝ // 0 < δ}

private theorem direction_sum_ne (z w : PacketDirection) : conj z.val+w.val ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hr
  linarith only [hr, z.property, w.property]

/-- The Hilbert inner product of two heat vectors is the partition at their combined parameter. -/
theorem groundState_overlap_zeta (s w : HeatVectorDomain) :
    inner ℂ (groundState s.val) (groundState w.val) = riemannZeta (conj s.val+w.val) := by
  let q : {z : ℂ // 1 < z.re} := ⟨conj s.val+w.val, by
    simp only [Complex.add_re, Complex.conj_re]
    linarith only [s.property, w.property]⟩
  change _ = riemannZeta q.val
  rw [lp.inner_eq_tsum, ← partition_eq_zeta q, gibbsOperator, HilbertSchmidt.opTrace_diagOp_comp]
  apply tsum_congr
  intro n
  rw [RCLike.inner_apply, groundState_apply s.property, groundState_apply w.property,
    ← heat_eq_cpow, ← heat_eq_cpow, ← heat_add, add_halves]
  change heat w.val n * conj (heat s.val n) = heat (conj s.val+w.val) n
  rw [heat_add, mul_comm]
  congr 1
  simp only [heat, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]

private def packetParameter (t : ℝ) (z : PacketDirection) (δ : PacketScale) : HeatVectorDomain :=
  ⟨1/2 + (t : ℂ)*Complex.I + (δ.val : ℂ)*z.val, by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    linarith only [mul_pos δ.property z.property]⟩

/-- Residue scaling makes the packet Gram matrix converge before individual normalization. -/
def residuePacket (t : ℝ) (z : PacketDirection) (δ : PacketScale) : Gas :=
  (Real.sqrt δ.val : ℂ) • groundState (packetParameter t z δ).val

private theorem residuePacket_ne_zero (t : ℝ) (z : PacketDirection) (δ : PacketScale) :
    residuePacket t z δ ≠ 0 :=
  smul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr δ.property).ne')
    (groundState_ne_zero (packetParameter t z δ).property)

/-- Positive scales tending to zero. -/
def packetPole : Filter PacketScale := comap Subtype.val (𝓝[>] (0:ℝ))

instance : NeBot packetPole := by
  change NeBot (comap ((↑) : PacketScale → ℝ) (𝓝[>] (0:ℝ)))
  rw [comap_neBot_iff_frequently]
  have hp : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  exact hp.frequently.mono (fun δ hδ => ⟨⟨δ,hδ⟩,rfl⟩)

private theorem scale_zero : Tendsto (fun δ : PacketScale => (δ.val : ℂ)) packetPole (𝓝 0) := by
  have hr : Tendsto ((↑) : PacketScale → ℝ) packetPole (𝓝 0) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  simpa only [Complex.ofReal_zero, Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hr

theorem residuePacket_overlap (t u : ℝ) (z w : PacketDirection) (δ : PacketScale) :
    inner ℂ (residuePacket t z δ) (residuePacket u w δ) =
      δ.val * riemannZeta (1 + ((u-t : ℝ) : ℂ)*Complex.I + (δ.val : ℂ)*(conj z.val+w.val)) := by
  rw [residuePacket, residuePacket, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt δ.property.le,
    groundState_overlap_zeta (packetParameter t z δ) (packetParameter u w δ)]
  apply congrArg (fun x : ℂ => (δ.val : ℂ) * riemannZeta x)
  simp only [packetParameter, map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_sub]
  ring

/-- Critical-line packets at one center have the half-plane Cauchy kernel.
Packets at distinct fixed clock centers become orthogonal. -/
theorem residuePacket_limit (t u : ℝ) (z w : PacketDirection) :
    Tendsto (fun δ => inner ℂ (residuePacket t z δ) (residuePacket u w δ)) packetPole
      (𝓝 (if t=u then (conj z.val+w.val)⁻¹ else 0)) := by
  let v := conj z.val+w.val
  have hv : v ≠ 0 := direction_sum_ne z w
  let q := 1 + ((u-t : ℝ) : ℂ)*Complex.I
  have hq : Tendsto (fun δ : PacketScale => q + (δ.val : ℂ)*v) packetPole (𝓝 q) := by
    simpa only [zero_mul, add_zero] using (tendsto_const_nhds (x := q)).add (scale_zero.mul_const v)
  by_cases he : t=u
  · subst u
    have hq1 : q = 1 := by simp [q]
    rw [hq1] at hq
    have hp : Tendsto (fun δ : PacketScale => 1 + (δ.val : ℂ)*v) packetPole (𝓝[≠] 1) :=
      tendsto_nhdsWithin_iff.mpr ⟨hq, Eventually.of_forall fun δ heq =>
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr δ.property.ne') hv)
          (add_eq_left.mp heq)⟩
    have hl := (riemannZeta_residue_one.comp hp).div_const v
    rw [if_pos rfl, ← one_div]
    apply hl.congr (fun δ => ?_)
    rw [residuePacket_overlap]
    change ((1+(δ.val : ℂ)*v-1)*riemannZeta (1+(δ.val : ℂ)*v)) / v =
      (δ.val : ℂ)*riemannZeta (q+(δ.val : ℂ)*v)
    rw [hq1, add_sub_cancel_left]
    field_simp
  · rw [if_neg he]
    have hne : q ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [q, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add] at hi
      exact he (sub_eq_zero.mp hi).symm
    have hl := scale_zero.mul ((differentiableAt_riemannZeta hne).continuousAt.tendsto.comp hq)
    rw [zero_mul] at hl
    exact hl.congr fun δ => (residuePacket_overlap t u z w δ).symm

/-- Unit packet centered at t, observed at distance δ·Re z from the critical line. -/
def unitClockPacket (t : ℝ) (z : PacketDirection) (δ : PacketScale) : Gas :=
  ((‖residuePacket t z δ‖ : ℂ)⁻¹) • residuePacket t z δ

theorem unitClockPacket_norm (t : ℝ) (z : PacketDirection) (δ : PacketScale) :
    ‖unitClockPacket t z δ‖ = 1 := by
  rw [unitClockPacket, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (residuePacket_ne_zero t z δ))]

private theorem residuePacket_norm_limit (t : ℝ) (z : PacketDirection) :
    Tendsto (fun δ => ‖residuePacket t z δ‖) packetPole (𝓝 ((Real.sqrt (2*z.val.re))⁻¹)) := by
  have hl := (Complex.continuous_re.tendsto _).comp (residuePacket_limit t t z z)
  have hc : conj z.val+z.val = ((2*z.val.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [if_pos rfl, hc, ← Complex.ofReal_inv, Complex.ofReal_re] at hl
  have hs : Tendsto (fun δ => ‖residuePacket t z δ‖^2) packetPole (𝓝 ((2*z.val.re)⁻¹)) := by
    apply hl.congr (fun δ => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (residuePacket t z δ)
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_inv] using
    (Real.continuous_sqrt.tendsto _).comp hs

/-- The normalized limiting Gram kernel separates clock centers. -/
theorem unitClockPacket_overlap_limit (t u : ℝ) (z w : PacketDirection) :
    Tendsto (fun δ => inner ℂ (unitClockPacket t z δ) (unitClockPacket u w δ))
      (comap Subtype.val (𝓝[>] (0:ℝ)))
      (𝓝 (if t=u then ((Real.sqrt (2*z.val.re)*Real.sqrt (2*w.val.re) : ℝ) : ℂ) /
        (conj z.val+w.val) else 0)) := by
  have hs (r : ℝ) (d : PacketDirection) : Tendsto
      (fun δ => ((‖residuePacket r d δ‖ : ℂ)⁻¹)) packetPole (𝓝 (Real.sqrt (2*d.val.re) : ℂ)) := by
    have hn : Real.sqrt (2*d.val.re) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos zero_lt_two d.property)).ne'
    have h := ((Complex.continuous_ofReal.tendsto _).comp (residuePacket_norm_limit r d)).inv₀
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hn))
    simpa only [Complex.ofReal_inv, inv_inv, Function.comp_def] using h
  have h := ((hs t z).mul (hs u w)).mul (residuePacket_limit t u z w)
  have hk : (Real.sqrt (2*z.val.re) : ℂ) * (Real.sqrt (2*w.val.re) : ℂ) *
      (if t=u then (conj z.val+w.val)⁻¹ else 0) =
      (if t=u then ((Real.sqrt (2*z.val.re)*Real.sqrt (2*w.val.re) : ℝ) : ℂ) /
        (conj z.val+w.val) else 0) := by
    by_cases he : t = u <;> simp only [he, if_true, if_false, Complex.ofReal_mul, div_eq_mul_inv, mul_zero]
  rw [hk] at h
  apply h.congr (fun δ => ?_)
  simp only [unitClockPacket, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal,
    mul_assoc, mul_left_comm]

/-- Within a single center, projective infidelity converges to squared
pseudohyperbolic distance in the right half-plane of packet directions. -/
theorem clockPacket_infidelity_limit (t : ℝ) (z w : PacketDirection) :
    Tendsto (fun δ => 1 - ‖inner ℂ (unitClockPacket t z δ) (unitClockPacket t w δ)‖^2)
      packetPole (𝓝 (‖z.val-w.val‖^2 / ‖conj z.val+w.val‖^2)) := by
  have h := unitClockPacket_overlap_limit t t z w
  rw [if_pos rfl] at h
  have hid : ‖conj z.val+w.val‖^2 = ‖z.val-w.val‖^2 + 4*z.val.re*w.val.re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  have hs := (tendsto_const_nhds (x := (1:ℝ))).sub (h.norm.pow 2)
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    mul_pow, Real.sq_sqrt (mul_nonneg zero_le_two z.property.le),
    Real.sq_sqrt (mul_nonneg zero_le_two w.property.le)] at hs
  have he : 1 - (2*z.val.re)*(2*w.val.re)/‖conj z.val+w.val‖^2 =
      ‖z.val-w.val‖^2/‖conj z.val+w.val‖^2 := by
    field_simp [norm_ne_zero_iff.mpr (direction_sum_ne z w)]
    linarith only [hid]
  rw [he] at hs
  exact hs

#print axioms groundState_overlap_zeta
#print axioms residuePacket_overlap
#print axioms residuePacket_limit
#print axioms unitClockPacket_norm
#print axioms unitClockPacket_overlap_limit
#print axioms clockPacket_infidelity_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
