import GaloisForLFunctions.HTGeometry.FDNLS.CouplingCoefficient

/-!
# The conserved power and Hamiltonian of a discrete NLS lattice

Zhong--Malomed--Yan, arXiv:2407.12441, Section II A, equations (16)--(18).

The fractional discrete nonlinear Schrödinger equation

`i u̇_n = C ∑_m D_{nm} u_m - σ |u_n|² u_n`

conserves the power `P = ∑_n |u_n|²` and the Hamiltonian
`H = ∑_n (C u_n^* (Du)_n - (σ/2)|u_n|⁴)`.  Both conservation laws are consequences of one structural
fact only: the coupling kernel is real and symmetric.  They are therefore proved here for an
arbitrary finite lattice with an arbitrary real symmetric kernel, and then specialised to the
quasi-Riesz kernel `D_{nm} = D_{n-m}^{(α)}` of equation (10) on the truncated lattice that the
paper's numerics use.

The whole computation runs through two real bilinear pairings on `ℂ`, the real and imaginary parts
of `⟨z, w⟩ = z̄ w`; the first is symmetric, the second antisymmetric, and every cancellation in the
proof is an antisymmetric double sum against a symmetric kernel.

## Main results

* `rePair`, `imPair` — the two real pairings and their calculus.
* `latticeNLSField`, `IsLatticeNLSSolution` — **equation (16)**.
* `latticePower`, `latticeHamiltonian` — **equations (18) and (17)**.
* `hasDerivAt_latticePower`, `latticePower_const` — conservation of the power.
* `hasDerivAt_latticeHamiltonian`, `latticeHamiltonian_const` — conservation of the Hamiltonian.
* `quasiRieszKernel_symm` — the quasi-Riesz kernel is symmetric, so both laws apply to the FDNLS
  lattice itself.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## The two real pairings -/

/-- The real part of the Hermitian pairing `⟨z, w⟩ = z̄ w`. -/
def rePair (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

/-- The imaginary part of the Hermitian pairing `⟨z, w⟩ = z̄ w`. -/
def imPair (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

theorem rePair_eq (z w : ℂ) : rePair z w = ((starRingEnd ℂ) z * w).re := by
  simp [rePair, Complex.mul_re]

theorem imPair_eq (z w : ℂ) : imPair z w = ((starRingEnd ℂ) z * w).im := by
  simp [imPair, Complex.mul_im]; ring

theorem rePair_comm (z w : ℂ) : rePair z w = rePair w z := by simp [rePair]; ring

theorem imPair_antisymm (z w : ℂ) : imPair z w = -imPair w z := by simp [imPair]; ring

theorem imPair_self (z : ℂ) : imPair z z = 0 := by simp [imPair]; ring

theorem rePair_self (z : ℂ) : rePair z z = ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [rePair, Complex.normSq_apply]

/-- Multiplying the second argument by `-i` exchanges the two pairings. -/
theorem rePair_neg_I_mul (z w : ℂ) : rePair z (-Complex.I * w) = imPair z w := by
  simp [rePair, imPair, Complex.mul_re, Complex.mul_im]; ring

theorem imPair_sum_right {κ : Type*} (s : Finset κ) (z : ℂ) (f : κ → ℂ) :
    imPair z (∑ m ∈ s, f m) = ∑ m ∈ s, imPair z (f m) := by
  classical
  induction s using Finset.induction with
  | empty => simp [imPair]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; simp [imPair]; ring

theorem imPair_sub_right (z w₁ w₂ : ℂ) : imPair z (w₁ - w₂) = imPair z w₁ - imPair z w₂ := by
  simp [imPair]; ring

theorem imPair_ofReal_mul (c : ℝ) (z w : ℂ) : imPair z ((c : ℂ) * w) = c * imPair z w := by
  simp [imPair, Complex.mul_re, Complex.mul_im]; ring

/-! ## Differentiating the pairings -/

theorem hasDerivAt_rePair {f g : ℝ → ℂ} {f' g' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => rePair (f s) (g s)) (rePair f' (g t) + rePair (f t) g') t := by
  have hfr : HasDerivAt (fun s => (f s).re) f'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hfi : HasDerivAt (fun s => (f s).im) f'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hgr : HasDerivAt (fun s => (g s).re) g'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
  have hgi : HasDerivAt (fun s => (g s).im) g'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hg
  have h := (hfr.mul hgr).add (hfi.mul hgi)
  simp only [Pi.mul_def, Pi.add_def] at h
  refine h.congr_deriv ?_
  simp [rePair]
  ring

theorem hasDerivAt_normSqPair {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * rePair (f t) f') t := by
  have h2 := hasDerivAt_rePair h h
  have h3 : (fun s => rePair (f s) (f s)) = fun s => ‖f s‖ ^ 2 :=
    funext fun s => rePair_self (f s)
  rw [h3] at h2
  refine h2.congr_deriv ?_
  rw [rePair_comm f' (f t)]
  ring

/-! ## Antisymmetric double sums -/

/-- An antisymmetric kernel has vanishing total sum over a finite square. -/
theorem sum_sum_antisymm {κ : Type*} [Fintype κ] (a : κ → κ → ℝ) (ha : ∀ n m, a n m = -a m n) :
    ∑ n, ∑ m, a n m = 0 := by
  have h1 : ∑ n : κ, ∑ m : κ, a n m = ∑ n : κ, ∑ m : κ, a m n := Finset.sum_comm
  have h2 : ∑ n : κ, ∑ m : κ, a m n = -∑ n : κ, ∑ m : κ, a n m := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => ha m n
  linarith [h1.trans h2]

theorem mul_const_mul_sum {κ : Type*} [Fintype κ] (c d : ℝ) (f : κ → ℝ) :
    d * (c * ∑ p : κ, f p) = c * ∑ p : κ, d * f p := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem sum_sum_sub {κ : Type*} [Fintype κ] (a b : κ → κ → ℝ) :
    (∑ n : κ, ∑ m : κ, (a n m - b n m))
      = (∑ n : κ, ∑ m : κ, a n m) - ∑ n : κ, ∑ m : κ, b n m := by
  simp [Finset.sum_sub_distrib]

theorem sum_sum_const_mul {κ : Type*} [Fintype κ] (c : ℝ) (a : κ → κ → ℝ) :
    (∑ n : κ, ∑ m : κ, c * a n m) = c * ∑ n : κ, ∑ m : κ, a n m := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]

/-- Differentiating a finite sum of real functions of a real variable. -/
theorem hasDerivAt_finsetSum {κ : Type*} [Fintype κ] {A : κ → ℝ → ℝ} {A' : κ → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (A i) (A' i) t) :
    HasDerivAt (fun s => ∑ i : κ, A i s) (∑ i : κ, A' i) t := by
  have h2 := HasDerivAt.sum (u := (Finset.univ : Finset κ)) (fun i _ => h i)
  have hfun : (∑ i : κ, A i) = fun s => ∑ i : κ, A i s := by
    funext s; simp [Finset.sum_apply]
  rwa [hfun] at h2

/-! ## The lattice model -/

variable {ι : Type*} [Fintype ι]

/-- **Equation (16).**  The right-hand side of a discrete NLS lattice with real coupling kernel
`D`, coupling constant `C` and nonlinearity sign `σ`. -/
noncomputable def latticeNLSField (C σ : ℝ) (D : ι → ι → ℝ) (u : ι → ℂ) (n : ι) : ℂ :=
  (C : ℂ) * (∑ m, ((D n m : ℝ) : ℂ) * u m) - ((σ * ‖u n‖ ^ 2 : ℝ) : ℂ) * u n

/-- A time-dependent lattice function solving `i u̇ = latticeNLSField`. -/
def IsLatticeNLSSolution (C σ : ℝ) (D : ι → ι → ℝ) (u : ℝ → ι → ℂ) : Prop :=
  ∀ (t : ℝ) (n : ι), HasDerivAt (fun s => u s n) (-Complex.I * latticeNLSField C σ D (u t) n) t

/-- **Equation (18).**  The power (norm). -/
noncomputable def latticePower (u : ι → ℂ) : ℝ := ∑ n, ‖u n‖ ^ 2

/-- **Equation (17).**  The Hamiltonian (energy). -/
noncomputable def latticeHamiltonian (C σ : ℝ) (D : ι → ι → ℝ) (u : ι → ℂ) : ℝ :=
  C * (∑ n, ∑ m, D n m * rePair (u n) (u m)) - σ / 2 * ∑ n, ‖u n‖ ^ 4

theorem imPair_latticeNLSField (C σ : ℝ) (D : ι → ι → ℝ) (u : ι → ℂ) (n m : ι) :
    imPair (u n) (latticeNLSField C σ D u m)
      = C * (∑ p, D m p * imPair (u n) (u p)) - σ * ‖u m‖ ^ 2 * imPair (u n) (u m) := by
  rw [latticeNLSField, imPair_sub_right, imPair_ofReal_mul, imPair_sum_right, imPair_ofReal_mul]
  have h : (∑ p, imPair (u n) (((D m p : ℝ) : ℂ) * u p)) = ∑ p, D m p * imPair (u n) (u p) :=
    Finset.sum_congr rfl fun p _ => imPair_ofReal_mul _ _ _
  rw [h]

/-- The square of a symmetric kernel is symmetric, so it too annihilates an antisymmetric
pairing. -/
theorem sum_triple_eq_zero (D : ι → ι → ℝ) (hD : ∀ n m, D n m = D m n) (u : ι → ℂ) :
    ∑ n, ∑ m, ∑ p, D n m * D m p * imPair (u n) (u p) = 0 := by
  have hstep : ∀ n : ι, (∑ m : ι, ∑ p : ι, D n m * D m p * imPair (u n) (u p))
      = ∑ p : ι, (∑ m : ι, D n m * D m p) * imPair (u n) (u p) := by
    intro n
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl fun n _ => hstep n]
  refine sum_sum_antisymm _ fun n p => ?_
  rw [imPair_antisymm (u n) (u p)]
  have hE : (∑ m : ι, D n m * D m p) = ∑ m : ι, D p m * D m n := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hD n m, hD m p]
    ring
  rw [hE]
  ring

/-! ## Conservation of the power -/

/-- The pointwise time derivative of the power vanishes identically. -/
theorem power_derivative_zero (C σ : ℝ) (D : ι → ι → ℝ) (hD : ∀ n m, D n m = D m n) (w : ι → ℂ) :
    (∑ n, 2 * rePair (w n) (-Complex.I * latticeNLSField C σ D w n)) = 0 := by
  have hterm : ∀ n : ι, 2 * rePair (w n) (-Complex.I * latticeNLSField C σ D w n)
      = ∑ m : ι, (2 * C) * (D n m * imPair (w n) (w m)) := by
    intro n
    rw [rePair_neg_I_mul, imPair_latticeNLSField, imPair_self, mul_zero, sub_zero]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl fun n _ => hterm n, sum_sum_const_mul,
    sum_sum_antisymm _ (fun n m => by rw [hD n m, imPair_antisymm (w n) (w m)]; ring), mul_zero]

/-- **Conservation of the power, equation (18).** -/
theorem hasDerivAt_latticePower {C σ : ℝ} {D : ι → ι → ℝ} (hD : ∀ n m, D n m = D m n)
    {u : ℝ → ι → ℂ} (hu : IsLatticeNLSSolution C σ D u) (t : ℝ) :
    HasDerivAt (fun s => latticePower (u s)) 0 t := by
  have hd : HasDerivAt (fun s => ∑ n : ι, ‖u s n‖ ^ 2)
      (∑ n : ι, 2 * rePair (u t n) (-Complex.I * latticeNLSField C σ D (u t) n)) t := by
    exact hasDerivAt_finsetSum (A := fun n s => ‖u s n‖ ^ 2) fun n => hasDerivAt_normSqPair (hu t n)
  rw [power_derivative_zero C σ D hD (u t)] at hd
  exact hd

/-- The power is constant along the flow. -/
theorem latticePower_const {C σ : ℝ} {D : ι → ι → ℝ} (hD : ∀ n m, D n m = D m n)
    {u : ℝ → ι → ℂ} (hu : IsLatticeNLSSolution C σ D u) (t₁ t₂ : ℝ) :
    latticePower (u t₁) = latticePower (u t₂) :=
  is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_latticePower hD hu t).differentiableAt)
    (fun t => (hasDerivAt_latticePower hD hu t).deriv) t₁ t₂

/-! ## Conservation of the Hamiltonian -/

/-- The pointwise time derivative of the Hamiltonian vanishes identically.  Every term cancels
against an antisymmetric double sum: the quadratic part against `D`, the quartic part against
`D²`. -/
theorem hamiltonian_derivative_zero (C σ : ℝ) (D : ι → ι → ℝ) (hD : ∀ n m, D n m = D m n)
    (w : ι → ℂ) :
    C * (∑ n, ∑ m, D n m * (rePair (-Complex.I * latticeNLSField C σ D w n) (w m)
        + rePair (w n) (-Complex.I * latticeNLSField C σ D w m)))
      - σ / 2 * (∑ n, 2 * ‖w n‖ ^ 2 * (2 * rePair (w n)
          (-Complex.I * latticeNLSField C σ D w n))) = 0 := by
  set F : ι → ℂ := fun n => latticeNLSField C σ D w n with hF
  have hAterm : ∀ n m : ι,
      D n m * (rePair (-Complex.I * F n) (w m) + rePair (w n) (-Complex.I * F m))
        = D n m * imPair (w m) (F n) + D n m * imPair (w n) (F m) := by
    intro n m
    rw [rePair_comm (-Complex.I * F n) (w m), rePair_neg_I_mul, rePair_neg_I_mul]
    ring
  have hA : (∑ n : ι, ∑ m : ι, D n m * (rePair (-Complex.I * F n) (w m)
        + rePair (w n) (-Complex.I * F m)))
      = 2 * ∑ n : ι, ∑ m : ι, D n m * imPair (w n) (F m) := by
    have h1 : (∑ n : ι, ∑ m : ι, D n m * (rePair (-Complex.I * F n) (w m)
          + rePair (w n) (-Complex.I * F m)))
        = (∑ n : ι, ∑ m : ι, D n m * imPair (w m) (F n))
          + ∑ n : ι, ∑ m : ι, D n m * imPair (w n) (F m) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => hAterm n m
    have h2 : (∑ n : ι, ∑ m : ι, D n m * imPair (w m) (F n))
        = ∑ n : ι, ∑ m : ι, D n m * imPair (w n) (F m) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      rw [hD m n]
    rw [h1, h2]
    ring
  have hB : (∑ n : ι, 2 * ‖w n‖ ^ 2 * (2 * rePair (w n) (-Complex.I * F n)))
      = ∑ n : ι, ∑ m : ι, (4 * C) * (‖w n‖ ^ 2 * (D n m * imPair (w n) (w m))) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [rePair_neg_I_mul, hF]
    simp only
    rw [imPair_latticeNLSField, imPair_self, mul_zero, sub_zero]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hG : (∑ n : ι, ∑ m : ι, D n m * imPair (w n) (F m))
      = -(σ * ∑ n : ι, ∑ m : ι, D n m * (‖w m‖ ^ 2 * imPair (w n) (w m))) := by
    have hexp : ∀ n m : ι, D n m * imPair (w n) (F m)
        = C * (∑ p : ι, D n m * D m p * imPair (w n) (w p))
          - σ * (D n m * (‖w m‖ ^ 2 * imPair (w n) (w m))) := by
      intro n m
      rw [hF]
      simp only
      rw [imPair_latticeNLSField, mul_sub, mul_const_mul_sum]
      congr 1
      · exact congrArg _ (Finset.sum_congr rfl fun p _ => by ring)
      · ring
    have hstep : (∑ n : ι, ∑ m : ι, D n m * imPair (w n) (F m))
        = ∑ n : ι, ∑ m : ι, (C * (∑ p : ι, D n m * D m p * imPair (w n) (w p))
            - σ * (D n m * (‖w m‖ ^ 2 * imPair (w n) (w m)))) :=
      Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hexp n m
    rw [hstep, sum_sum_sub, sum_sum_const_mul, sum_sum_const_mul,
      sum_triple_eq_zero D hD w, mul_zero, zero_sub]
  have hfin : (∑ n : ι, ∑ m : ι, D n m * (‖w m‖ ^ 2 * imPair (w n) (w m)))
      + ∑ n : ι, ∑ m : ι, ‖w n‖ ^ 2 * (D n m * imPair (w n) (w m)) = 0 := by
    rw [← Finset.sum_add_distrib]
    have hcomb : ∀ n : ι, (∑ m : ι, D n m * (‖w m‖ ^ 2 * imPair (w n) (w m)))
        + ∑ m : ι, ‖w n‖ ^ 2 * (D n m * imPair (w n) (w m))
        = ∑ m : ι, D n m * imPair (w n) (w m) * (‖w m‖ ^ 2 + ‖w n‖ ^ 2) := by
      intro n
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun n _ => hcomb n]
    refine sum_sum_antisymm _ fun n m => ?_
    rw [hD n m, imPair_antisymm (w n) (w m)]
    ring
  rw [hA, hB, hG, sum_sum_const_mul]
  have hUV : (∑ n : ι, ∑ m : ι, ‖w n‖ ^ 2 * (D n m * imPair (w n) (w m)))
      = -(∑ n : ι, ∑ m : ι, D n m * (‖w m‖ ^ 2 * imPair (w n) (w m))) := by linarith [hfin]
  rw [hUV]
  ring

/-- **Conservation of the Hamiltonian, equation (17).** -/
theorem hasDerivAt_latticeHamiltonian {C σ : ℝ} {D : ι → ι → ℝ} (hD : ∀ n m, D n m = D m n)
    {u : ℝ → ι → ℂ} (hu : IsLatticeNLSSolution C σ D u) (t : ℝ) :
    HasDerivAt (fun s => latticeHamiltonian C σ D (u s)) 0 t := by
  have hinner : ∀ n : ι, HasDerivAt (fun s => ∑ m : ι, D n m * rePair (u s n) (u s m))
      (∑ m : ι, D n m * (rePair (-Complex.I * latticeNLSField C σ D (u t) n) (u t m)
        + rePair (u t n) (-Complex.I * latticeNLSField C σ D (u t) m))) t := fun n =>
    hasDerivAt_finsetSum (A := fun m s => D n m * rePair (u s n) (u s m))
      fun m => HasDerivAt.const_mul (D n m) (hasDerivAt_rePair (hu t n) (hu t m))
  have hd1 : HasDerivAt (fun s => ∑ n : ι, ∑ m : ι, D n m * rePair (u s n) (u s m))
      (∑ n : ι, ∑ m : ι, D n m * (rePair (-Complex.I * latticeNLSField C σ D (u t) n) (u t m)
        + rePair (u t n) (-Complex.I * latticeNLSField C σ D (u t) m))) t :=
    hasDerivAt_finsetSum (A := fun n s => ∑ m : ι, D n m * rePair (u s n) (u s m)) hinner
  have hquart : ∀ n : ι, HasDerivAt (fun s => ‖u s n‖ ^ 4)
      (2 * ‖u t n‖ ^ 2 * (2 * rePair (u t n)
        (-Complex.I * latticeNLSField C σ D (u t) n))) t := by
    intro n
    have hp := (hasDerivAt_normSqPair (hu t n)).pow 2
    have hfun : ((fun s => ‖u s n‖ ^ 2) ^ (2 : ℕ) : ℝ → ℝ) = fun s => ‖u s n‖ ^ 4 := by
      funext s
      simp only [Pi.pow_apply]
      ring
    rw [hfun] at hp
    refine hp.congr_deriv ?_
    norm_num
  have hd2 : HasDerivAt (fun s => ∑ n : ι, ‖u s n‖ ^ 4)
      (∑ n : ι, 2 * ‖u t n‖ ^ 2 * (2 * rePair (u t n)
        (-Complex.I * latticeNLSField C σ D (u t) n))) t :=
    hasDerivAt_finsetSum (A := fun n s => ‖u s n‖ ^ 4) hquart
  have hd := (hd1.const_mul C).sub (hd2.const_mul (σ / 2))
  rw [hamiltonian_derivative_zero C σ D hD (u t)] at hd
  exact hd

/-- The Hamiltonian is constant along the flow. -/
theorem latticeHamiltonian_const {C σ : ℝ} {D : ι → ι → ℝ} (hD : ∀ n m, D n m = D m n)
    {u : ℝ → ι → ℂ} (hu : IsLatticeNLSSolution C σ D u) (t₁ t₂ : ℝ) :
    latticeHamiltonian C σ D (u t₁) = latticeHamiltonian C σ D (u t₂) :=
  is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_latticeHamiltonian hD hu t).differentiableAt)
    (fun t => (hasDerivAt_latticeHamiltonian hD hu t).deriv) t₁ t₂

/-! ## The quasi-Riesz lattice -/

/-- The quasi-Riesz kernel on a finite window of the lattice: `D_{nm} = D_{n-m}^{(α)}`. -/
noncomputable def quasiRieszKernel (α : ℝ) {N : ℕ} (i j : Fin N) : ℝ :=
  quasiRieszCoupling α ((i : ℤ) - (j : ℤ))

/-- The quasi-Riesz kernel is symmetric, because the coupling coefficients are even.  Hence both
conservation laws above apply verbatim to the truncated FDNLS lattice. -/
theorem quasiRieszKernel_symm (α : ℝ) {N : ℕ} (i j : Fin N) :
    quasiRieszKernel α i j = quasiRieszKernel α j i := by
  rw [quasiRieszKernel, quasiRieszKernel, ← quasiRieszCoupling_neg α ((i : ℤ) - (j : ℤ))]
  congr 1
  ring

/-- **Equations (17) and (18) for the FDNLS lattice.**  Power and Hamiltonian are conserved by the
truncated fractional discrete nonlinear Schrödinger flow. -/
theorem quasiRiesz_conserved {C σ α : ℝ} {N : ℕ} {u : ℝ → Fin N → ℂ}
    (hu : IsLatticeNLSSolution C σ (quasiRieszKernel α) u) (t₁ t₂ : ℝ) :
    latticePower (u t₁) = latticePower (u t₂)
      ∧ latticeHamiltonian C σ (quasiRieszKernel α) (u t₁)
        = latticeHamiltonian C σ (quasiRieszKernel α) (u t₂) :=
  ⟨latticePower_const (quasiRieszKernel_symm α) hu t₁ t₂,
    latticeHamiltonian_const (quasiRieszKernel_symm α) hu t₁ t₂⟩

end GaloisForLFunctions.HTGeometry.FDNLS
