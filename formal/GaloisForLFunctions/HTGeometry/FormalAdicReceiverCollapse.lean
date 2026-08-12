import GaloisForLFunctions.HTGeometry.WienerFormationScale
import GaloisForLFunctions.HTGeometry.FormationScaleReceiver

/-!
# Collapse of the continuous complex receivers of the formal packet ring

Give `ℂ⟦T⟧` the `T`-adic topology, whose zero neighbourhoods are the ideals `(T^n)`.  Then every
scalar renormalisation `c_n T^n` tends to zero however fast `c_n` grows, and the truncations of a
packet converge to it.  Consequently a continuous unital complex character kills `T` and is
constant-term evaluation: the purely formal completion preserves the algebra but retains only one
analytic receiver.
-/

namespace HTGeometry

open PowerSeries Filter

/-- The `T`-adic ideal of the formal packets. -/
noncomputable def formalAdicIdeal : Ideal (PowerSeries ℂ) :=
  Ideal.span {(X : PowerSeries ℂ)}

theorem mem_formalAdicIdeal_pow {n : ℕ} {f : PowerSeries ℂ} :
    f ∈ formalAdicIdeal ^ n ↔ ∀ m < n, (PowerSeries.coeff m) f = 0 := by
  rw [formalAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton, X_pow_dvd_iff]

/-- **The formal topology sees no coefficient growth.**  Every scalar renormalisation of the powers
of `T` tends to zero `T`-adically. -/
theorem formalAdic_tendsto_smul_X_pow (c : ℕ → ℂ) :
    Tendsto (fun n => c n • (X : PowerSeries ℂ) ^ n) atTop
      (@nhds _ formalAdicIdeal.adicTopology 0) := by
  rw [(formalAdicIdeal.hasBasis_nhds_zero_adic).tendsto_right_iff]
  intro k _
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [SetLike.mem_coe, mem_formalAdicIdeal_pow]
  intro m hm
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, if_neg (by omega), smul_zero]

/-- **The truncations converge `T`-adically.** -/
theorem formalAdic_tendsto_trunc (f : PowerSeries ℂ) :
    Tendsto (fun N => wienerScaleTrunc N f) atTop
      (@nhds _ formalAdicIdeal.adicTopology f) := by
  rw [(formalAdicIdeal.hasBasis_nhds_adic f).tendsto_right_iff]
  intro k _
  filter_upwards [eventually_ge_atTop k] with N hN
  refine ⟨wienerScaleTrunc N f - f, ?_, by ring⟩
  rw [SetLike.mem_coe, mem_formalAdicIdeal_pow]
  intro m hm
  rw [map_sub, coeff_wienerScaleTrunc, if_pos (by omega), sub_self]

/-- **A continuous formal receiver kills the generator.** -/
theorem formalAdicCharacter_apply_X (χ : PowerSeries ℂ →ₐ[ℂ] ℂ)
    (hχ : @Continuous _ _ formalAdicIdeal.adicTopology _ χ) : χ X = 0 := by
  letI := formalAdicIdeal.adicTopology
  refine GaloisForLFunctions.HTGeometry.continuous_receiver_kills_formal_generator χ hχ X ?_
  have h := formalAdic_tendsto_smul_X_pow (fun n => (χ X)⁻¹ ^ n)
  refine h.congr fun n => ?_
  rw [Algebra.smul_def]

/-- **Formal receiver collapse.**  Every `T`-adically continuous unital complex character of the
formal packet ring is constant-term evaluation. -/
theorem formalAdicCharacter_eq_constantCoeff (χ : PowerSeries ℂ →ₐ[ℂ] ℂ)
    (hχ : @Continuous _ _ formalAdicIdeal.adicTopology _ χ) (f : PowerSeries ℂ) :
    χ f = PowerSeries.constantCoeff f := by
  letI := formalAdicIdeal.adicTopology
  have hX : χ X = 0 := formalAdicCharacter_apply_X χ hχ
  have hC : ∀ c : ℂ, χ (PowerSeries.C c) = c := by
    intro c
    have h := χ.commutes c
    simpa [PowerSeries.algebraMap_apply] using h
  have htrunc : ∀ N : ℕ, 1 ≤ N →
      χ (wienerScaleTrunc N f) = PowerSeries.constantCoeff f := by
    intro N hN
    rw [wienerScaleTrunc, map_sum,
      Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
    · rw [map_mul, map_pow, hX, pow_zero, mul_one, hC]
      simp
    · intro n _ hn
      rw [map_mul, map_pow, hX, zero_pow hn, mul_zero]
  have hconv : Tendsto (fun N => χ (wienerScaleTrunc N f)) atTop (nhds (χ f)) :=
    (hχ.tendsto f).comp (formalAdic_tendsto_trunc f)
  have hconst : Tendsto (fun N => χ (wienerScaleTrunc N f)) atTop
      (nhds (PowerSeries.constantCoeff f)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (htrunc N hN).symm
  exact tendsto_nhds_unique hconv hconst

/-- **Only one receiver survives.**  The `T`-adically continuous characters of `ℂ⟦T⟧` are exactly
the constant-term evaluation, so no nonzero receiver point is admitted. -/
theorem formalAdicCharacter_unique (χ ψ : PowerSeries ℂ →ₐ[ℂ] ℂ)
    (hχ : @Continuous _ _ formalAdicIdeal.adicTopology _ χ)
    (hψ : @Continuous _ _ formalAdicIdeal.adicTopology _ ψ) : χ = ψ := by
  refine AlgHom.ext fun f => ?_
  rw [formalAdicCharacter_eq_constantCoeff χ hχ f, formalAdicCharacter_eq_constantCoeff ψ hψ f]

end HTGeometry
