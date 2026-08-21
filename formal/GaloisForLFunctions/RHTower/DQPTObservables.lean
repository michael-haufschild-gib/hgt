import GaloisForLFunctions.RHTower.DQPTPartitionRate

/-!
# DQPT: the engineered observables and their closed forms

Main text of arXiv:2511.11199, equations (2), (3), (4)–(5), and Methods equation (22).

The system has the logarithmic spectrum `Eₙ = log n`, thermal state `ρ_s = e^{−βH₀}/Z(β,H₀)`,
and the probe reads out the **average accumulated phase factor**

`L(β,t) = Tr(ρ_s e^{−iH₀t} σ_z¹) = ∑_{n=1}^N (−1)ⁿ e^{−iEₙt} e^{−βEₙ}/Z(β,H₀)`.

Main results:
* `dqptPhaseFactor_eq` — **main text (2)**: `L(β,t) = −S_N(β+it)/Z(β,H₀)`;
* `dqpt_partition_mul_phaseFactor_tendsto` — **main text (3)**:
  `Z(β,H₀)·L(β,t) → (2^{1−s} − 1)ζ(s)`;
* `dqpt_norm_sq_sqrtState`, `dqpt_inner_eq_partition_mul_phaseFactor` — **main text (4)–(5)**:
  the Choi–Jamiołkowski boundary partition function equals `Z·L`;
* `dqptLoschmidtAmplitude_eq` — **Methods (22)**.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## The logarithmic spectrum and the thermal weights -/

/-- The logarithmic energy spectrum `Eₙ = log n`. -/
def dqptEnergy (n : ℕ) : ℝ := Real.log n

theorem dqpt_exp_energy {n : ℕ} (hn : 1 ≤ n) (β : ℝ) :
    Real.exp (-β * dqptEnergy n) = (n : ℝ) ^ (-β) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [dqptEnergy, Real.rpow_def_of_pos hn0, mul_comm]

/-- The phase-and-weight factor of level `n` is `n^{−(β+it)}`. -/
theorem dqpt_phase_weight_eq {n : ℕ} (hn : 1 ≤ n) (β t : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy n : ℝ) : ℂ))
        * ((Real.exp (-β * dqptEnergy n) : ℝ) : ℂ)
      = dqptRp ((β : ℂ) + (t : ℂ) * Complex.I) (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hn0)
  have hlog : Complex.log ((n : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hn0)).symm
  rw [dqptRp, Complex.cpow_def_of_ne_zero hne, hlog, dqptEnergy,
    show ((Real.exp (-β * Real.log n) : ℝ) : ℂ) = Complex.exp (((-β * Real.log n : ℝ)) : ℂ) by
      rw [Complex.ofReal_exp],
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The average accumulated phase factor -/

/-- `L(β,t) = Tr(ρ_s e^{−iH₀t}σ_z¹)`, the average accumulated phase factor. -/
def dqptPhaseFactor (β t : ℝ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N,
      (-1 : ℂ) ^ n * (Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy n : ℝ) : ℂ))
        * ((Real.exp (-β * dqptEnergy n) : ℝ) : ℂ)))
    / ((dqptPartition β N : ℝ) : ℂ)

theorem dqpt_sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ i ∈ Finset.range N, f (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])

theorem dqptAltPartialSum_eq_sum_Icc (s : ℂ) (N : ℕ) :
    dqptAltPartialSum s N = ∑ n ∈ Finset.Icc 1 N, (-1 : ℂ) ^ (n + 1) * dqptRp s (n : ℝ) := by
  rw [dqptAltPartialSum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hc : ((1 + i : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [hc]
  congr 1
  rw [pow_succ, pow_add]
  ring

/-- **Main text (2).**  `L(β,t) = −S_N(β+it)/Z(β,H₀)`. -/
theorem dqptPhaseFactor_eq (β t : ℝ) (N : ℕ) :
    dqptPhaseFactor β t N
      = -dqptAltPartialSum ((β : ℂ) + (t : ℂ) * Complex.I) N
          / ((dqptPartition β N : ℝ) : ℂ) := by
  rw [dqptPhaseFactor, dqptAltPartialSum_eq_sum_Icc]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (-1 : ℂ) ^ n * (Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy n : ℝ) : ℂ))
        * ((Real.exp (-β * dqptEnergy n) : ℝ) : ℂ))
      = -((-1 : ℂ) ^ (n + 1) * dqptRp ((β : ℂ) + (t : ℂ) * Complex.I) (n : ℝ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [dqpt_phase_weight_eq hn.1 β t, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, neg_div]

/-- **Main text (3).**  `Z(β,H₀)·L(β,t) → (2^{1−s} − 1)ζ(s)` in the thermodynamic limit. -/
theorem dqpt_partition_mul_phaseFactor_tendsto {β t : ℝ} (hβ : 0 < β)
    (hs1 : (β : ℂ) + (t : ℂ) * Complex.I ≠ 1) :
    Tendsto (fun N : ℕ => ((dqptPartition β N : ℝ) : ℂ) * dqptPhaseFactor β t N) atTop
      (𝓝 (((2 : ℂ) ^ (1 - ((β : ℂ) + (t : ℂ) * Complex.I)) - 1)
        * riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I))) := by
  have hre : ((β : ℂ) + (t : ℂ) * Complex.I).re = β := by simp
  have hlim := (dqpt_altPartialSum_tendsto (s := (β : ℂ) + (t : ℂ) * Complex.I)
    (by rw [hre]; exact hβ) hs1).neg
  have hval : -((1 - (2 : ℂ) ^ (1 - ((β : ℂ) + (t : ℂ) * Complex.I)))
      * riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I))
      = ((2 : ℂ) ^ (1 - ((β : ℂ) + (t : ℂ) * Complex.I)) - 1)
        * riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I) := by ring
  rw [hval] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hZ : ((dqptPartition β N : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < dqptPartition β N :=
      lt_of_lt_of_le zero_lt_one (one_le_dqptPartition β hN)
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  rw [dqptPhaseFactor_eq]
  field_simp

/-! ## Main text (4)–(5): the Choi–Jamiołkowski boundary partition function -/

/-- The square-root-weighted boundary state `|ψ_a⟩ ∝ ∑ₙ n^{−β/2}|n⟩|n⟩ₐ`, in the system register. -/
def dqptSqrtState (β : ℝ) (N : ℕ) : EuclideanSpace ℂ (Fin N) :=
  (WithLp.equiv 2 (Fin N → ℂ)).symm
    (fun k => ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (-β / 2) : ℝ))

@[simp] theorem dqptSqrtState_apply (β : ℝ) (N : ℕ) (k : Fin N) :
    dqptSqrtState β N k = ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (-β / 2) : ℝ) := rfl

/-- The parity-flipped boundary state `|ψ_b⟩ = σ_z¹|ψ_a⟩`. -/
def dqptParityState (β : ℝ) (N : ℕ) : EuclideanSpace ℂ (Fin N) :=
  (WithLp.equiv 2 (Fin N → ℂ)).symm
    (fun k => (-1 : ℂ) ^ ((k : ℕ) + 1) * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (-β / 2) : ℝ))

@[simp] theorem dqptParityState_apply (β : ℝ) (N : ℕ) (k : Fin N) :
    dqptParityState β N k
      = (-1 : ℂ) ^ ((k : ℕ) + 1) * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (-β / 2) : ℝ) := rfl

/-- The bulk evolution `e^{−iH₀t}` acting diagonally on the system register. -/
def dqptEvolve (t : ℝ) (N : ℕ) (v : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  (WithLp.equiv 2 (Fin N → ℂ)).symm
    (fun k => Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy ((k : ℕ) + 1) : ℝ) : ℂ)) * v k)

@[simp] theorem dqptEvolve_apply (t : ℝ) (N : ℕ) (v : EuclideanSpace ℂ (Fin N)) (k : Fin N) :
    dqptEvolve t N v k
      = Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy ((k : ℕ) + 1) : ℝ) : ℂ)) * v k := rfl

/-- **Main text (4).**  The boundary state has squared norm equal to the partition function. -/
theorem dqpt_norm_sq_sqrtState (β : ℝ) (N : ℕ) :
    ‖dqptSqrtState β N‖ ^ 2 = dqptPartition β N := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), dqptPartition_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range (fun n : ℕ => ((n : ℝ) + 1) ^ (-β)) N]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hpos : (0 : ℝ) < (((k : ℕ) : ℝ) + 1) := by positivity
  have hval : ‖dqptSqrtState β N k‖ = (((k : ℕ) : ℝ) + 1) ^ (-β / 2) := by
    rw [dqptSqrtState_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    congr 1
    push_cast
    ring
  rw [hval, ← Real.rpow_natCast ((((k : ℕ) : ℝ) + 1) ^ (-β / 2)) 2,
    ← Real.rpow_mul (le_of_lt hpos)]
  norm_num

/-- **Main text (5).**  The analytically continued boundary partition function
`Z_B(β, it, H₀⊗I) = ⟨ψ_a|(e^{−iH₀t}⊗I)|ψ_b⟩` equals `Z(β,H₀)·L(β,t)`. -/
theorem dqpt_inner_eq_partition_mul_phaseFactor (β t : ℝ) (N : ℕ) :
    (inner ℂ (dqptSqrtState β N) (dqptEvolve t N (dqptParityState β N)) : ℂ)
      = ((dqptPartition β N : ℝ) : ℂ) * dqptPhaseFactor β t N := by
  have hZ : ((dqptPartition β N : ℝ) : ℂ) * dqptPhaseFactor β t N
      = ∑ n ∈ Finset.Icc 1 N,
          (-1 : ℂ) ^ n * (Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy n : ℝ) : ℂ))
            * ((Real.exp (-β * dqptEnergy n) : ℝ) : ℂ)) := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [dqptPhaseFactor, dqptPartition]
    · have hpos : (0 : ℝ) < dqptPartition β N :=
        lt_of_lt_of_le zero_lt_one (one_le_dqptPartition β hN)
      have hne : ((dqptPartition β N : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      rw [dqptPhaseFactor]
      field_simp
  rw [hZ, PiLp.inner_apply, dqpt_sum_Icc_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range (fun n : ℕ =>
      (-1 : ℂ) ^ (n + 1) * (Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy (n + 1) : ℝ) : ℂ))
        * ((Real.exp (-β * dqptEnergy (n + 1)) : ℝ) : ℂ))) N]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hn1 : 1 ≤ (k : ℕ) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hposr : (0 : ℝ) < ((((k : ℕ) + 1 : ℕ)) : ℝ) := by positivity
  have hsplit : ((Real.exp (-β * dqptEnergy ((k : ℕ) + 1)) : ℝ) : ℂ)
      = ((((((k : ℕ) + 1 : ℕ)) : ℝ) ^ (-β / 2) : ℝ) : ℂ)
        * ((((((k : ℕ) + 1 : ℕ)) : ℝ) ^ (-β / 2) : ℝ) : ℂ) := by
    have hexp : (-β / 2) + (-β / 2) = -β := by ring
    rw [← Complex.ofReal_mul, ← Real.rpow_add hposr, hexp, dqpt_exp_energy hn1 β]
  simp only [RCLike.inner_apply, dqptEvolve_apply, dqptParityState_apply, dqptSqrtState_apply,
    Complex.conj_ofReal]
  rw [hsplit]
  ring_nf

/-! ## Methods (22): the Loschmidt readout -/

/-- `S(t) = Tr[e^{−iA(t)}ρ_s]` with `A(t) = H₀t − θ(t)`. -/
def dqptLoschmidtAmplitude (θ β t : ℝ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N,
      Complex.exp (Complex.I * (θ : ℂ))
        * (Complex.exp (-Complex.I * (t : ℂ) * ((dqptEnergy n : ℝ) : ℂ))
          * ((Real.exp (-β * dqptEnergy n) : ℝ) : ℂ)))
    / ((dqptPartition β N : ℝ) : ℂ)

/-- **Methods (22).**  `S(t) = e^{iθ(t)}·(1/Z)·∑_{n≤N} n^{−β−it}`. -/
theorem dqptLoschmidtAmplitude_eq (θ β t : ℝ) (N : ℕ) :
    dqptLoschmidtAmplitude θ β t N
      = Complex.exp (Complex.I * (θ : ℂ))
        * (∑ n ∈ Finset.Icc 1 N, dqptRp ((β : ℂ) + (t : ℂ) * Complex.I) (n : ℝ))
          / ((dqptPartition β N : ℝ) : ℂ) := by
  rw [dqptLoschmidtAmplitude]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_Icc] at hn
  rw [dqpt_phase_weight_eq hn.1 β t]

end

end RHTower.DQPT
