import GaloisForLFunctions.HTGeometry.FDNLS.Operator
import GaloisForLFunctions.HTGeometry.FDNLS.Conservation

/-!
# The two exact symmetries of the FDNLS lattice

Zhong--Malomed--Yan, arXiv:2407.12441, Section II A/B, equations (21) and (27).

* **The staggering transform, equation (21).**  At Lévy index `α = 1` the coupling coefficients
  vanish at every even separation and change sign at every odd one, so the substitution
  `u_n(t) = (-1)^n q_n^*(t) e^{-iCπ t}` exchanges the self-focusing and self-defocusing equations.
  The whole mechanism is the coefficient identity
  `(-1)^ℓ D_ℓ^{(1)} = π·[ℓ = 0] - D_ℓ^{(1)}`, proved here from the closed form of equation (14).
* **The scaling reduction, equation (27).**  A negative frequency scales out of the stationary
  equation (26), which is why the paper fixes `ω = -1` and keeps `C` as the only parameter.

## Main results

* `quasiRieszCoupling_one_stagger` — the coefficient identity behind equation (21).
* `quasiRieszKernel_one_stagger` — the same identity for the truncated lattice kernel.
* `stagger`, `stagger_involutive` — the transform of equation (21) and its involutivity.
* `stagger_solution`, `stagger_solution_iff` — **equation (21)**: staggering exchanges `σ` and `-σ`.
* `quasiRiesz_stagger_solution_iff` — the same statement for the `α = 1` FDNLS lattice itself.
* `stationary_scaling` — **equation (27)**.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## The staggering identity for the coupling coefficients -/

/-- **The mechanism behind equation (21).**  At `α = 1` the alternating coupling table is the
diagonal-corrected negative of the coupling table: `(-1)^ℓ D_ℓ^{(1)} = π·[ℓ = 0] - D_ℓ^{(1)}`.
Off the diagonal this says the even coefficients vanish and the odd ones change sign. -/
theorem quasiRieszCoupling_one_stagger (ℓ : ℤ) :
    (-1 : ℝ) ^ ℓ * quasiRieszCoupling 1 ℓ
      = (if ℓ = 0 then Real.pi else 0) - quasiRieszCoupling 1 ℓ := by
  have hsq : ((-1 : ℝ)) ^ ℓ * ((-1 : ℝ)) ^ ℓ = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1:ℝ) ≠ 0), ← two_mul, zpow_mul]
    norm_num
  by_cases h : ℓ = 0
  · subst h
    rw [if_pos rfl, quasiRieszCoupling_one_zero, zpow_zero, one_mul]
    ring
  · rw [if_neg h, quasiRieszCoupling_one h]
    have hl : ((ℓ : ℝ)) ≠ 0 := Int.cast_ne_zero.2 h
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    nlinarith [hsq]

/-- The alternating sign as a function of the lattice site. -/
noncomputable def staggerSign {N : ℕ} (i : Fin N) : ℝ := (-1 : ℝ) ^ (i : ℕ)

theorem staggerSign_mul_self {N : ℕ} (i : Fin N) : staggerSign i * staggerSign i = 1 := by
  rw [staggerSign, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **Equation (21) for the truncated `α = 1` lattice kernel.** -/
theorem quasiRieszKernel_one_stagger {N : ℕ} (i m : Fin N) :
    staggerSign i * staggerSign m * quasiRieszKernel 1 i m
      = (if i = m then Real.pi else 0) - quasiRieszKernel 1 i m := by
  have hsign : staggerSign i * staggerSign m = (-1 : ℝ) ^ ((i : ℤ) - (m : ℤ)) := by
    have hm : ((-1 : ℝ)) ^ ((m : ℤ)) * ((-1 : ℝ)) ^ ((m : ℤ)) = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1:ℝ) ≠ 0), ← two_mul, zpow_mul]
      norm_num
    rw [zpow_sub₀ (by norm_num : (-1:ℝ) ≠ 0), staggerSign, staggerSign]
    rw [← zpow_natCast (-1 : ℝ) (i : ℕ), ← zpow_natCast (-1 : ℝ) (m : ℕ)]
    field_simp
    nlinarith [hm]
  rw [hsign, quasiRieszKernel]
  have hif : (if ((i : ℤ) - (m : ℤ)) = 0 then Real.pi else 0)
      = (if i = m then Real.pi else 0) := by
    by_cases h : i = m
    · rw [h, if_pos rfl, if_pos (by ring)]
    · rw [if_neg h, if_neg]
      intro hc
      exact h (Fin.ext (by omega))
  rw [← hif]
  exact quasiRieszCoupling_one_stagger _

/-! ## The staggering transform -/

/-- The time phase `e^{-i r t}` of equation (21). -/
noncomputable def staggerPhase (r t : ℝ) : ℂ := Complex.exp (-(Complex.I * (r : ℂ)) * (t : ℂ))

theorem staggerPhase_re (r t : ℝ) : (-(Complex.I * (r : ℂ)) * (t : ℂ)).re = 0 := by
  simp [Complex.mul_re]

theorem norm_staggerPhase (r t : ℝ) : ‖staggerPhase r t‖ = 1 := by
  rw [staggerPhase, Complex.norm_exp, staggerPhase_re]
  exact Real.exp_zero

theorem staggerPhase_conj_mul (r t : ℝ) :
    (starRingEnd ℂ) (staggerPhase r t) * staggerPhase r t = 1 := by
  rw [staggerPhase, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (-(Complex.I * (r : ℂ)) * (t : ℂ)) + -(Complex.I * (r : ℂ)) * (t : ℂ)
      = 0 := by
    rw [add_comm, Complex.add_conj, staggerPhase_re]
    norm_num
  rw [h, Complex.exp_zero]

theorem hasDerivAt_staggerPhase (r t : ℝ) :
    HasDerivAt (staggerPhase r) (staggerPhase r t * -(Complex.I * (r : ℂ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(Complex.I * (r : ℂ)) * (s : ℂ))
      (-(Complex.I * (r : ℂ))) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (-(Complex.I * (r : ℂ)))
  exact h1.cexp

theorem hasDerivAt_conjComp {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (starRingEnd ℂ) (f s)) ((starRingEnd ℂ) f') t :=
  Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **Equation (21).**  The staggering transform `q ↦ (-1)^n q^* e^{-iCκ t}`. -/
noncomputable def stagger (C κ : ℝ) (ε : ι → ℝ) (q : ℝ → ι → ℂ) (t : ℝ) (n : ι) : ℂ :=
  ((ε n : ℝ) : ℂ) * (starRingEnd ℂ) (q t n) * staggerPhase (C * κ) t

omit [Fintype ι] [DecidableEq ι] in
/-- The staggering transform is an involution. -/
theorem stagger_involutive {C κ : ℝ} {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) (q : ℝ → ι → ℂ) :
    stagger C κ ε (stagger C κ ε q) = q := by
  funext t n
  simp only [stagger]
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have hεn : ((ε n : ℝ) : ℂ) * ((ε n : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hε n, Complex.ofReal_one]
  have hP := staggerPhase_conj_mul (C * κ) t
  calc ((ε n : ℝ) : ℂ) * (((ε n : ℝ) : ℂ) * q t n * (starRingEnd ℂ) (staggerPhase (C * κ) t))
        * staggerPhase (C * κ) t
      = (((ε n : ℝ) : ℂ) * ((ε n : ℝ) : ℂ))
        * ((starRingEnd ℂ) (staggerPhase (C * κ) t) * staggerPhase (C * κ) t) * q t n := by ring
  _ = q t n := by rw [hεn, hP]; ring

omit [Fintype ι] [DecidableEq ι] in
theorem norm_stagger {C κ : ℝ} {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) (q : ℝ → ι → ℂ)
    (t : ℝ) (n : ι) : ‖stagger C κ ε q t n‖ = ‖q t n‖ := by
  have habs : |ε n| = 1 := by
    have h := hε n
    nlinarith [abs_nonneg (ε n), sq_abs (ε n)]
  rw [stagger, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, habs,
    norm_staggerPhase, RCLike.norm_conj]
  ring

/-- The staggering identity, transported to the coupling sum. -/
theorem stagger_sum {κ : ℝ} {D : ι → ι → ℝ} {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hstag : ∀ i m, ε i * ε m * D i m = (if i = m then κ else 0) - D i m) (x : ι → ℂ) (n : ι) :
    (∑ m, ((D n m : ℝ) : ℂ) * (((ε m : ℝ) : ℂ) * x m))
      = ((ε n : ℝ) : ℂ) * ((κ : ℂ) * x n - ∑ m, ((D n m : ℝ) : ℂ) * x m) := by
  have hpt : ∀ m : ι, D n m * ε m = ε n * ((if n = m then κ else 0) - D n m) := by
    intro m
    have h := hstag n m
    have hn := hε n
    linear_combination (ε n) * h - (D n m * ε m) * hn
  have hstep : ∀ m : ι, ((D n m : ℝ) : ℂ) * (((ε m : ℝ) : ℂ) * x m)
      = ((ε n : ℝ) : ℂ) * ((if n = m then (κ : ℂ) * x m else 0)
        - ((D n m : ℝ) : ℂ) * x m) := by
    intro m
    have h := hpt m
    by_cases hm : n = m
    · rw [if_pos hm] at h ⊢
      have hc : ((D n m : ℝ) : ℂ) * ((ε m : ℝ) : ℂ)
          = ((ε n : ℝ) : ℂ) * ((κ : ℂ) - ((D n m : ℝ) : ℂ)) := by
        have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
        push_cast at hcast
        exact hcast
      calc ((D n m : ℝ) : ℂ) * (((ε m : ℝ) : ℂ) * x m)
          = (((D n m : ℝ) : ℂ) * ((ε m : ℝ) : ℂ)) * x m := by ring
      _ = (((ε n : ℝ) : ℂ) * ((κ : ℂ) - ((D n m : ℝ) : ℂ))) * x m := by rw [hc]
      _ = ((ε n : ℝ) : ℂ) * ((κ : ℂ) * x m - ((D n m : ℝ) : ℂ) * x m) := by ring
    · rw [if_neg hm] at h ⊢
      have hc : ((D n m : ℝ) : ℂ) * ((ε m : ℝ) : ℂ)
          = ((ε n : ℝ) : ℂ) * (0 - ((D n m : ℝ) : ℂ)) := by
        have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
        push_cast at hcast
        exact hcast
      calc ((D n m : ℝ) : ℂ) * (((ε m : ℝ) : ℂ) * x m)
          = (((D n m : ℝ) : ℂ) * ((ε m : ℝ) : ℂ)) * x m := by ring
      _ = (((ε n : ℝ) : ℂ) * (0 - ((D n m : ℝ) : ℂ))) * x m := by rw [hc]
      _ = ((ε n : ℝ) : ℂ) * (0 - ((D n m : ℝ) : ℂ) * x m) := by ring
  rw [Finset.sum_congr rfl fun m _ => hstep m, ← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 2
  rw [Finset.sum_ite_eq Finset.univ n fun m => (κ : ℂ) * x m]
  simp

/-- **Equation (21).**  Staggering carries a solution with nonlinearity sign `-σ` to a solution with
nonlinearity sign `σ`. -/
theorem stagger_solution {C σ κ : ℝ} {D : ι → ι → ℝ} {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hstag : ∀ i m, ε i * ε m * D i m = (if i = m then κ else 0) - D i m)
    {q : ℝ → ι → ℂ} (hq : IsLatticeNLSSolution C (-σ) D q) :
    IsLatticeNLSSolution C σ D (stagger C κ ε q) := by
  intro t n
  have hd := ((hasDerivAt_conjComp (hq t n)).mul (hasDerivAt_staggerPhase (C * κ) t)).const_mul
    (((ε n : ℝ) : ℂ))
  simp only [Pi.mul_def] at hd
  have hfun : (fun s : ℝ =>
      ((ε n : ℝ) : ℂ) * ((starRingEnd ℂ) (q s n) * staggerPhase (C * κ) s))
      = fun s : ℝ => stagger C κ ε q s n := by
    funext s
    rw [stagger]
    ring
  rw [hfun] at hd
  refine hd.congr_deriv ?_
  have hnorm : ‖stagger C κ ε q t n‖ = ‖q t n‖ := norm_stagger hε q t n
  have hconjF : (starRingEnd ℂ) (latticeNLSField C (-σ) D (q t) n)
      = (C : ℂ) * (∑ m, ((D n m : ℝ) : ℂ) * (starRingEnd ℂ) (q t m))
        + ((σ * ‖q t n‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (q t n) := by
    rw [latticeNLSField, map_sub, map_mul, map_mul, map_sum, Complex.conj_ofReal,
      Complex.conj_ofReal]
    have hcm : ∀ m : ι, (starRingEnd ℂ) (((D n m : ℝ) : ℂ) * q t m)
        = ((D n m : ℝ) : ℂ) * (starRingEnd ℂ) (q t m) := by
      intro m
      rw [map_mul, Complex.conj_ofReal]
    rw [Finset.sum_congr rfl fun m _ => hcm m]
    push_cast
    ring
  have hfield : latticeNLSField C σ D (stagger C κ ε q t) n
      = staggerPhase (C * κ) t * (((ε n : ℝ) : ℂ)
        * ((C : ℂ) * ((κ : ℂ) * (starRingEnd ℂ) (q t n)
            - ∑ m, ((D n m : ℝ) : ℂ) * (starRingEnd ℂ) (q t m))
          - ((σ * ‖q t n‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (q t n))) := by
    rw [latticeNLSField, hnorm]
    have hsum : (∑ m, ((D n m : ℝ) : ℂ) * stagger C κ ε q t m)
        = staggerPhase (C * κ) t * (((ε n : ℝ) : ℂ) * ((κ : ℂ) * (starRingEnd ℂ) (q t n)
            - ∑ m, ((D n m : ℝ) : ℂ) * (starRingEnd ℂ) (q t m))) := by
      have hrw : ∀ m : ι, ((D n m : ℝ) : ℂ) * stagger C κ ε q t m
          = staggerPhase (C * κ) t
            * (((D n m : ℝ) : ℂ) * (((ε m : ℝ) : ℂ) * (starRingEnd ℂ) (q t m))) := by
        intro m
        rw [stagger]
        ring
      rw [Finset.sum_congr rfl fun m _ => hrw m, ← Finset.mul_sum,
        stagger_sum hε hstag (fun m => (starRingEnd ℂ) (q t m)) n]
    rw [hsum, stagger]
    ring
  rw [hfield]
  rw [show (starRingEnd ℂ) (-Complex.I * latticeNLSField C (-σ) D (q t) n)
      = Complex.I * (starRingEnd ℂ) (latticeNLSField C (-σ) D (q t) n) by
    rw [map_mul]
    simp]
  rw [hconjF]
  push_cast
  ring

/-- Staggering exchanges the two signs of the nonlinearity, in both directions. -/
theorem stagger_solution_iff {C σ κ : ℝ} {D : ι → ι → ℝ} {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hstag : ∀ i m, ε i * ε m * D i m = (if i = m then κ else 0) - D i m) (q : ℝ → ι → ℂ) :
    IsLatticeNLSSolution C σ D (stagger C κ ε q) ↔ IsLatticeNLSSolution C (-σ) D q := by
  refine ⟨fun h => ?_, stagger_solution hε hstag⟩
  have h2 := stagger_solution (σ := -σ) hε hstag (by simpa using h)
  rwa [stagger_involutive hε q] at h2

/-- **Equation (21) for the FDNLS lattice at `α = 1`.**  The self-focusing and self-defocusing
truncated fractional discrete NLS equations are equivalent. -/
theorem quasiRiesz_stagger_solution_iff {C σ : ℝ} {N : ℕ} (q : ℝ → Fin N → ℂ) :
    IsLatticeNLSSolution C σ (quasiRieszKernel 1)
        (stagger C Real.pi staggerSign q)
      ↔ IsLatticeNLSSolution C (-σ) (quasiRieszKernel 1) q :=
  stagger_solution_iff staggerSign_mul_self quasiRieszKernel_one_stagger q

/-! ## The scaling reduction -/

/-- **Equation (26).**  The stationary equation of the lattice. -/
def IsStationaryLattice (C ω : ℝ) (D : ι → ι → ℝ) (v : ι → ℂ) : Prop :=
  ∀ n, ((‖v n‖ ^ 2 + ω : ℝ) : ℂ) * v n = (C : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * v m

omit [DecidableEq ι] in
/-- **Equation (27).**  A negative frequency scales out of the stationary equation: solving it at
frequency `ω < 0` and coupling `C` is the same as solving it at frequency `-1` and coupling
`C/(-ω)`, after the amplitude rescaling `v = √(-ω) v̂`. -/
theorem stationary_scaling {C ω : ℝ} (hω : ω < 0) (D : ι → ι → ℝ) (v : ι → ℂ) :
    IsStationaryLattice C ω D (fun n => ((Real.sqrt (-ω) : ℝ) : ℂ) * v n)
      ↔ IsStationaryLattice (C / (-ω)) (-1) D v := by
  have hpos : (0:ℝ) < -ω := by linarith
  have hs : (0:ℝ) < Real.sqrt (-ω) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (-ω) ^ 2 = -ω := Real.sq_sqrt hpos.le
  have hsc : ((Real.sqrt (-ω) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hωc : ((-ω : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  have hω0 : (ω : ℂ) ≠ 0 := by exact_mod_cast ne_of_lt hω
  have hexp : (((C / (-ω) : ℝ)) : ℂ) * ((-ω : ℝ) : ℂ) = (C : ℂ) := by
    push_cast
    field_simp
  have hnorm : ∀ n, ‖((Real.sqrt (-ω) : ℝ) : ℂ) * v n‖ ^ 2 = -ω * ‖v n‖ ^ 2 := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow, hsq]
  have hkey : ∀ n : ι,
      (((‖((Real.sqrt (-ω) : ℝ) : ℂ) * v n‖ ^ 2 + ω : ℝ) : ℂ) * (((Real.sqrt (-ω) : ℝ) : ℂ) * v n)
        = (C : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * (((Real.sqrt (-ω) : ℝ) : ℂ) * v m))
      ↔ (((‖v n‖ ^ 2 + -1 : ℝ) : ℂ) * v n
        = (((C / (-ω) : ℝ)) : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * v m) := by
    intro n
    rw [hnorm n]
    have hleft : ((-ω * ‖v n‖ ^ 2 + ω : ℝ) : ℂ) * (((Real.sqrt (-ω) : ℝ) : ℂ) * v n)
        = (((Real.sqrt (-ω) : ℝ) : ℂ) * ((-ω : ℝ) : ℂ)) * (((‖v n‖ ^ 2 + -1 : ℝ) : ℂ) * v n) := by
      push_cast
      ring
    have hpull : ∀ c : ℂ, (∑ m, ((D n m : ℝ) : ℂ) * (c * v m))
        = c * ∑ m, ((D n m : ℝ) : ℂ) * v m := by
      intro c
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hright : (C : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * (((Real.sqrt (-ω) : ℝ) : ℂ) * v m)
        = (((Real.sqrt (-ω) : ℝ) : ℂ) * ((-ω : ℝ) : ℂ))
          * ((((C / (-ω) : ℝ)) : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * v m) := by
      rw [hpull,
        show (((Real.sqrt (-ω) : ℝ) : ℂ) * ((-ω : ℝ) : ℂ))
            * ((((C / (-ω) : ℝ)) : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * v m)
          = ((((C / (-ω) : ℝ)) : ℂ) * ((-ω : ℝ) : ℂ))
            * (((Real.sqrt (-ω) : ℝ) : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * v m) by ring, hexp]
    rw [hleft, hright]
    exact mul_right_inj' (mul_ne_zero hsc hωc)
  constructor
  · intro h n
    exact (hkey n).mp (h n)
  · intro h n
    exact (hkey n).mpr (h n)

end GaloisForLFunctions.HTGeometry.FDNLS
