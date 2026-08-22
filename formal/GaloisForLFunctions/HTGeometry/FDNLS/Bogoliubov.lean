import GaloisForLFunctions.HTGeometry.FDNLS.Conservation

/-!
# The Bogoliubov--de Gennes linearization

Zhong--Malomed--Yan, arXiv:2407.12441, Section II B, equations (28), (29) and (30).

Substituting the perturbed ansatz

`u_n(t) = e^{-iωt} (v_n + δ (a_n e^{λt} + b_n^* e^{λ^* t}))`

into the lattice equation and dividing out the carrier `e^{-iωt}` leaves a residual that depends on
the perturbation amplitude `δ`.  Its value at `δ = 0` is the stationary equation (26); its
derivative at `δ = 0` is the linearized operator of equation (30), and it vanishes for all times
exactly when the eigenvalue system (29) holds.

This file makes all three statements exact: the linearization is a genuine derivative, not a formal
`O(δ)` truncation, and the passage from (30) to (29) is the algebraic identity that the two
exponentials `e^{λt}` and `e^{λ^* t}` carry the two rows of (29).

## Main results

* `stationaryResidual` — the residual of equation (26).
* `bdgFirstOrder`, `hasDerivAt_stationaryResidual` — **equation (30)**: the exact linearization
  `L₁₁ w + L₁₂ w^*` of the lattice field.
* `bdgPerturbation`, `bdgResidual` — **equation (28)**.
* `IsBdGMode` — **equation (29)**.
* `hasDerivAt_bdgResidual` — the derivative of the residual in `δ`.
* `bdgFirstOrder_perturbation_eq_zero` — a Bogoliubov mode kills the first-order residual at every
  time.
* `bdgResidual_first_order_vanishes` — the full statement: for a stationary background and a
  Bogoliubov mode, the residual of equation (28) vanishes to first order in `δ`, uniformly in `t`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-- The polarisation identity behind equation (30): differentiating `|v|²v` produces
`2 Re⟨v, w⟩ v = |v|² w + v² w^*`. -/
theorem two_rePair_mul (z w : ℂ) :
    ((2 * rePair z w : ℝ) : ℂ) * z
      = ((‖z‖ ^ 2 : ℝ) : ℂ) * w + z ^ 2 * (starRingEnd ℂ) w := by
  rw [← rePair_self]
  refine Complex.ext ?_ ?_ <;>
    simp only [rePair, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, pow_two] <;> ring

variable {ι : Type*} [Fintype ι]

/-! ## The stationary residual and its linearization -/

/-- The residual of the stationary equation (26). -/
noncomputable def stationaryResidual (C σ ω : ℝ) (D : ι → ι → ℝ) (v : ι → ℂ) (n : ι) : ℂ :=
  (ω : ℂ) * v n + ((σ * ‖v n‖ ^ 2 : ℝ) : ℂ) * v n - (C : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * v m

/-- **Equation (30).**  The linearized operator: `L₁₁ w + L₁₂ w^*` with
`L₁₁ = C D - 2σ|v|² - ω` and `L₁₂ = -σ v²`, written here as the derivative of the residual. -/
noncomputable def bdgFirstOrder (C σ ω : ℝ) (D : ι → ι → ℝ) (v w : ι → ℂ) (n : ι) : ℂ :=
  (ω : ℂ) * w n
    + (σ : ℂ) * (2 * ((‖v n‖ ^ 2 : ℝ) : ℂ) * w n + (v n) ^ 2 * (starRingEnd ℂ) (w n))
    - (C : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * w m

theorem hasDerivAt_ofRealLin (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t :=
  (hasDerivAt_id t).ofReal_comp

/-- Differentiating a finite sum of complex-valued functions of a real variable. -/
theorem hasDerivAt_finsetSumC {κ : Type*} [Fintype κ] {A : κ → ℝ → ℂ} {A' : κ → ℂ} {t : ℝ}
    (h : ∀ i, HasDerivAt (A i) (A' i) t) :
    HasDerivAt (fun s => ∑ i : κ, A i s) (∑ i : κ, A' i) t := by
  have h2 := HasDerivAt.sum (u := (Finset.univ : Finset κ)) (fun i _ => h i)
  have hfun : (∑ i : κ, A i) = fun s => ∑ i : κ, A i s := by
    funext s; simp [Finset.sum_apply]
  rwa [hfun] at h2

/-- **Equation (30) as an exact derivative.**  The `δ`-derivative at `δ = 0` of the stationary
residual along the perturbation `w` is the Bogoliubov operator. -/
theorem hasDerivAt_stationaryResidual (C σ ω : ℝ) (D : ι → ι → ℝ) (v w : ι → ℂ) (n : ι) :
    HasDerivAt
      (fun δ : ℝ => stationaryResidual C σ ω D (fun m => v m + (δ : ℂ) * w m) n)
      (bdgFirstOrder C σ ω D v w n) 0 := by
  have hline : ∀ m : ι, HasDerivAt (fun δ : ℝ => v m + (δ : ℂ) * w m) (w m) 0 := by
    intro m
    have h := ((hasDerivAt_ofRealLin (0:ℝ)).mul_const (w m)).const_add (v m)
    simpa using h
  -- the frequency term
  have hω : HasDerivAt (fun δ : ℝ => (ω : ℂ) * (v n + (δ : ℂ) * w n)) ((ω : ℂ) * w n) 0 :=
    (hline n).const_mul (ω : ℂ)
  -- the coupling term
  have hsum : HasDerivAt (fun δ : ℝ => ∑ m, ((D n m : ℝ) : ℂ) * (v m + (δ : ℂ) * w m))
      (∑ m, ((D n m : ℝ) : ℂ) * w m) 0 :=
    hasDerivAt_finsetSumC (A := fun m δ => ((D n m : ℝ) : ℂ) * (v m + (δ : ℂ) * w m))
      fun m => (hline m).const_mul _
  have hC : HasDerivAt (fun δ : ℝ => (C : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * (v m + (δ : ℂ) * w m))
      ((C : ℂ) * ∑ m, ((D n m : ℝ) : ℂ) * w m) 0 :=
    hsum.const_mul (C : ℂ)
  -- the nonlinear term
  have hnormexp : ∀ δ : ℝ, ‖v n + (δ : ℂ) * w n‖ ^ 2
      = ‖v n‖ ^ 2 + 2 * δ * rePair (v n) (w n) + δ ^ 2 * ‖w n‖ ^ 2 := by
    intro δ
    rw [← rePair_self, ← rePair_self, ← rePair_self]
    simp only [rePair, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpoly : HasDerivAt
      (fun δ : ℝ => σ * (‖v n‖ ^ 2 + 2 * δ * rePair (v n) (w n) + δ ^ 2 * ‖w n‖ ^ 2))
      (σ * (2 * rePair (v n) (w n))) 0 := by
    have hbase : HasDerivAt
        (fun δ : ℝ => ‖v n‖ ^ 2 + 2 * δ * rePair (v n) (w n) + δ ^ 2 * ‖w n‖ ^ 2)
        (2 * rePair (v n) (w n)) 0 := by
      have h1 : HasDerivAt (fun δ : ℝ => 2 * δ * rePair (v n) (w n))
          (2 * rePair (v n) (w n)) 0 := by
        have := ((hasDerivAt_id (0:ℝ)).const_mul (2:ℝ)).mul_const (rePair (v n) (w n))
        simpa using this
      have h2 : HasDerivAt (fun δ : ℝ => δ ^ 2 * ‖w n‖ ^ 2) 0 0 := by
        have := ((hasDerivAt_pow 2 (0:ℝ))).mul_const (‖w n‖ ^ 2)
        simpa using this
      have h3 := (h1.const_add (‖v n‖ ^ 2)).add h2
      simp only [Pi.add_def, add_zero] at h3
      exact h3
    exact hbase.const_mul σ
  have hscalar : HasDerivAt (fun δ : ℝ => ((σ * ‖v n + (δ : ℂ) * w n‖ ^ 2 : ℝ)))
      (σ * (2 * rePair (v n) (w n))) 0 := by
    have hfun : (fun δ : ℝ => σ * (‖v n‖ ^ 2 + 2 * δ * rePair (v n) (w n) + δ ^ 2 * ‖w n‖ ^ 2))
        = fun δ : ℝ => ((σ * ‖v n + (δ : ℂ) * w n‖ ^ 2 : ℝ)) := by
      funext δ
      rw [hnormexp δ]
    rwa [hfun] at hpoly
  have hnl : HasDerivAt
      (fun δ : ℝ => ((σ * ‖v n + (δ : ℂ) * w n‖ ^ 2 : ℝ) : ℂ) * (v n + (δ : ℂ) * w n))
      ((((σ * (2 * rePair (v n) (w n))) : ℝ) : ℂ) * (v n + ((0:ℝ) : ℂ) * w n)
        + ((σ * ‖v n + ((0:ℝ) : ℂ) * w n‖ ^ 2 : ℝ) : ℂ) * w n) 0 :=
    (hscalar.ofReal_comp).mul (hline n)
  have hd := (hω.add hnl).sub hC
  refine hd.congr_deriv ?_
  have hzero : ((0:ℝ) : ℂ) = 0 := by norm_num
  rw [hzero]
  simp only [zero_mul, add_zero]
  rw [bdgFirstOrder]
  have hkey : ((σ * (2 * rePair (v n) (w n)) : ℝ) : ℂ) * v n
      = (σ : ℂ) * (((‖v n‖ ^ 2 : ℝ) : ℂ) * w n + (v n) ^ 2 * (starRingEnd ℂ) (w n)) := by
    have h2 := two_rePair_mul (v n) (w n)
    rw [show ((σ * (2 * rePair (v n) (w n)) : ℝ) : ℂ)
        = (σ : ℂ) * ((2 * rePair (v n) (w n) : ℝ) : ℂ) by push_cast; ring, mul_assoc, h2]
  rw [hkey]
  push_cast
  ring

/-! ## The perturbed ansatz -/

/-- **Equation (28).**  The perturbation `a_n e^{λt} + b_n^* e^{λ^* t}`. -/
noncomputable def bdgPerturbation (a b : ι → ℂ) (lam : ℂ) (t : ℝ) (n : ι) : ℂ :=
  a n * Complex.exp (lam * (t : ℂ))
    + (starRingEnd ℂ) (b n) * Complex.exp ((starRingEnd ℂ) lam * (t : ℂ))

/-- The time derivative of the perturbation. -/
noncomputable def bdgPerturbationDot (a b : ι → ℂ) (lam : ℂ) (t : ℝ) (n : ι) : ℂ :=
  lam * a n * Complex.exp (lam * (t : ℂ))
    + (starRingEnd ℂ) lam * (starRingEnd ℂ) (b n) * Complex.exp ((starRingEnd ℂ) lam * (t : ℂ))

/-- **Equation (28).**  The residual of the lattice equation for the perturbed ansatz, with the
carrier `e^{-iωt}` divided out. -/
noncomputable def bdgResidual (C σ ω : ℝ) (D : ι → ι → ℝ) (v a b : ι → ℂ) (lam : ℂ)
    (t : ℝ) (δ : ℝ) (n : ι) : ℂ :=
  stationaryResidual C σ ω D (fun m => v m + (δ : ℂ) * bdgPerturbation a b lam t m) n
    + Complex.I * (δ : ℂ) * bdgPerturbationDot a b lam t n

/-- At `δ = 0` the residual is exactly the stationary residual. -/
theorem bdgResidual_zero (C σ ω : ℝ) (D : ι → ι → ℝ) (v a b : ι → ℂ) (lam : ℂ) (t : ℝ) (n : ι) :
    bdgResidual C σ ω D v a b lam t 0 n = stationaryResidual C σ ω D v n := by
  rw [bdgResidual]
  norm_num

/-- The derivative of the residual in the perturbation amplitude. -/
theorem hasDerivAt_bdgResidual (C σ ω : ℝ) (D : ι → ι → ℝ) (v a b : ι → ℂ) (lam : ℂ)
    (t : ℝ) (n : ι) :
    HasDerivAt (fun δ : ℝ => bdgResidual C σ ω D v a b lam t δ n)
      (bdgFirstOrder C σ ω D v (bdgPerturbation a b lam t) n
        + Complex.I * bdgPerturbationDot a b lam t n) 0 := by
  have h1 := hasDerivAt_stationaryResidual C σ ω D v (bdgPerturbation a b lam t) n
  have h2 : HasDerivAt (fun δ : ℝ => Complex.I * (δ : ℂ) * bdgPerturbationDot a b lam t n)
      (Complex.I * bdgPerturbationDot a b lam t n) 0 := by
    have := ((hasDerivAt_ofRealLin (0:ℝ)).const_mul Complex.I).mul_const
      (bdgPerturbationDot a b lam t n)
    simpa using this
  exact h1.add h2

/-! ## The eigenvalue problem -/

/-- The operator `L₁₁ = C D - 2σ|v|² - ω` of equation (30). -/
noncomputable def bdgL11 (C σ ω : ℝ) (D : ι → ι → ℝ) (v x : ι → ℂ) (n : ι) : ℂ :=
  (C : ℂ) * (∑ m, ((D n m : ℝ) : ℂ) * x m)
    - ((2 * σ * ‖v n‖ ^ 2 : ℝ) : ℂ) * x n - (ω : ℂ) * x n

/-- The operator `L₁₂ = -σ v²` of equation (30). -/
noncomputable def bdgL12 (σ : ℝ) (v x : ι → ℂ) (n : ι) : ℂ := -(σ : ℂ) * (v n) ^ 2 * x n

/-- `L₁₁` has real coefficients, so it commutes with conjugation. -/
theorem conj_bdgL11 (C σ ω : ℝ) (D : ι → ι → ℝ) (v x : ι → ℂ) (n : ι) :
    (starRingEnd ℂ) (bdgL11 C σ ω D v x n)
      = bdgL11 C σ ω D v (fun m => (starRingEnd ℂ) (x m)) n := by
  have hc : ∀ m : ι, (starRingEnd ℂ) (((D n m : ℝ) : ℂ) * x m)
      = ((D n m : ℝ) : ℂ) * (starRingEnd ℂ) (x m) := by
    intro m
    rw [map_mul, Complex.conj_ofReal]
  rw [bdgL11, bdgL11, map_sub, map_sub, map_mul, map_mul, map_mul, map_sum,
    Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
    Finset.sum_congr rfl fun m _ => hc m]

/-- **Equation (29).**  The Bogoliubov--de Gennes eigenvalue problem. -/
def IsBdGMode (C σ ω : ℝ) (D : ι → ι → ℝ) (v a b : ι → ℂ) (lam : ℂ) : Prop :=
  (∀ n, bdgL11 C σ ω D v a n + bdgL12 σ v b n = Complex.I * lam * a n)
    ∧ (∀ n, (σ : ℂ) * ((starRingEnd ℂ) (v n)) ^ 2 * a n - bdgL11 C σ ω D v b n
        = Complex.I * lam * b n)

/-- Conjugating a real-time exponential flips the exponent. -/
theorem conj_exp_mul_ofReal (lam : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (Complex.exp (lam * (t : ℂ)))
      = Complex.exp ((starRingEnd ℂ) lam * (t : ℂ)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]

/-- **The passage from equation (30) to equation (29).**  A Bogoliubov mode annihilates the
first-order residual at every time: the coefficient of `e^{λt}` is the first row of (29) and the
coefficient of `e^{λ^*t}` is the conjugate of the second. -/
theorem bdgFirstOrder_perturbation_eq_zero {C σ ω : ℝ} {D : ι → ι → ℝ} {v a b : ι → ℂ} {lam : ℂ}
    (h : IsBdGMode C σ ω D v a b lam) (t : ℝ) (n : ι) :
    bdgFirstOrder C σ ω D v (bdgPerturbation a b lam t) n
      + Complex.I * bdgPerturbationDot a b lam t n = 0 := by
  obtain ⟨h1, h2⟩ := h
  have hconjP : (starRingEnd ℂ) (bdgPerturbation a b lam t n)
      = (starRingEnd ℂ) (a n) * Complex.exp ((starRingEnd ℂ) lam * (t : ℂ))
        + b n * Complex.exp (lam * (t : ℂ)) := by
    rw [bdgPerturbation, map_add, map_mul, map_mul, conj_exp_mul_ofReal, conj_exp_mul_ofReal,
      Complex.conj_conj, Complex.conj_conj]
  have hsumP : (∑ m, ((D n m : ℝ) : ℂ) * bdgPerturbation a b lam t m)
      = Complex.exp (lam * (t : ℂ)) * (∑ m, ((D n m : ℝ) : ℂ) * a m)
        + Complex.exp ((starRingEnd ℂ) lam * (t : ℂ))
          * ∑ m, ((D n m : ℝ) : ℂ) * (starRingEnd ℂ) (b m) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [bdgPerturbation]
    ring
  have hrow1 : (ω : ℂ) * a n
      + (σ : ℂ) * (2 * ((‖v n‖ ^ 2 : ℝ) : ℂ) * a n + (v n) ^ 2 * b n)
      - (C : ℂ) * (∑ m, ((D n m : ℝ) : ℂ) * a m) + Complex.I * (lam * a n) = 0 := by
    have hone := h1 n
    rw [bdgL11, bdgL12] at hone
    push_cast at hone ⊢
    linear_combination -hone
  have hrow2 : (ω : ℂ) * ((starRingEnd ℂ) (b n))
      + (σ : ℂ) * (2 * ((‖v n‖ ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (b n))
        + (v n) ^ 2 * ((starRingEnd ℂ) (a n)))
      - (C : ℂ) * (∑ m, ((D n m : ℝ) : ℂ) * (starRingEnd ℂ) (b m))
      + Complex.I * ((starRingEnd ℂ) lam * (starRingEnd ℂ) (b n)) = 0 := by
    have hc := congrArg (starRingEnd ℂ) (h2 n)
    rw [map_sub] at hc
    rw [conj_bdgL11] at hc
    simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj, Complex.conj_I] at hc
    rw [bdgL11] at hc
    push_cast at hc ⊢
    linear_combination hc
  rw [bdgFirstOrder, hsumP, hconjP, bdgPerturbation, bdgPerturbationDot]
  linear_combination Complex.exp (lam * (t : ℂ)) * hrow1
    + Complex.exp ((starRingEnd ℂ) lam * (t : ℂ)) * hrow2

/-- **Equations (28)--(30) together.**  For a stationary background and a Bogoliubov mode, the
residual of the perturbed ansatz vanishes at `δ = 0` and has vanishing derivative there, uniformly
in time: the mode is an exact solution of the linearized problem. -/
theorem bdgResidual_first_order_vanishes {C σ ω : ℝ} {D : ι → ι → ℝ} {v a b : ι → ℂ} {lam : ℂ}
    (hv : ∀ n, stationaryResidual C σ ω D v n = 0)
    (h : IsBdGMode C σ ω D v a b lam) (t : ℝ) (n : ι) :
    bdgResidual C σ ω D v a b lam t 0 n = 0
      ∧ HasDerivAt (fun δ : ℝ => bdgResidual C σ ω D v a b lam t δ n) 0 0 := by
  refine ⟨by rw [bdgResidual_zero]; exact hv n, ?_⟩
  have hd := hasDerivAt_bdgResidual C σ ω D v a b lam t n
  rwa [bdgFirstOrder_perturbation_eq_zero h t n] at hd

end GaloisForLFunctions.HTGeometry.FDNLS
