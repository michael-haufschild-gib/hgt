import GaloisForLFunctions.HTGeometry.EulerQGammaObserver

/-!
# The recurrent observer of the Euler q-Gamma process

`L²(ℕ_{>0}, P_σ)` is modelled by `ℓ²` with the cyclic vector `Ω = (√P_σ(m))`, and the unitary
group `U_t` acts by the phases `exp(i t X_σ(m))`.  The cyclic matrix coefficient is the
characteristic function of the random-integer law, which is the response at an imaginary argument;
and the orbit is recurrent: finitely many phases can be returned simultaneously close to one by a
compactness argument in a torus, and the remaining mass is uniformly small.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The `ℓ²` model -/

theorem summable_eqgMass (σ : EulerSigma) : Summable (eqgMass σ) :=
  (eqgMass_hasSum_one σ).summable

theorem eqgSqrt_memℓp (σ : EulerSigma) (φ : ℕ → ℂ) (hφ : ∀ m, ‖φ m‖ = 1) :
    Memℓp (fun m : ℕ => φ m * ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ)) 2 := by
  refine memℓp_gen ?_
  have hfun : (fun m : ℕ => ‖φ m * ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ)‖ ^ (2 : ENNReal).toReal)
      = eqgMass σ := by
    funext m
    rw [norm_mul, hφ m, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (eqgMass_nonneg σ m)]
  rw [hfun]
  exact summable_eqgMass σ

theorem eqgSqrt_memℓp' (σ : EulerSigma) :
    Memℓp (fun m : ℕ => ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ)) 2 := by
  have h := eqgSqrt_memℓp σ (fun _ => 1) (fun _ => by simp)
  simpa using h

/-- The cyclic vector `Ω = (√P_σ(m))` of the arithmetic process. -/
def eqgOmega (σ : EulerSigma) : QGammaSpace :=
  ⟨fun m => ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ), eqgSqrt_memℓp' σ⟩

theorem norm_eqgPhase (σ : EulerSigma) (t : ℝ) (m : ℕ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The orbit vector `U_t Ω`. -/
def eqgOrbit (σ : EulerSigma) (t : ℝ) : QGammaSpace :=
  ⟨fun m => Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ))
      * ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ),
    eqgSqrt_memℓp σ _ (norm_eqgPhase σ t)⟩

@[simp] theorem eqgOrbit_apply (σ : EulerSigma) (t : ℝ) (m : ℕ) :
    (eqgOrbit σ t : ℕ → ℂ) m
      = Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ))
        * ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ) := rfl

@[simp] theorem eqgOmega_apply (σ : EulerSigma) (m : ℕ) :
    (eqgOmega σ : ℕ → ℂ) m = ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ) := rfl

/-! ## The characteristic function -/

/-- The characteristic function of the random-integer law. -/
def eqgCharProc (σ : EulerSigma) (t : ℝ) : ℂ :=
  ∑' m : ℕ, ((eqgMass σ m : ℝ) : ℂ)
    * Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ))

theorem eqgCharProc_hasSum (σ : EulerSigma) (t : ℝ) :
    HasSum (fun m : ℕ => ((eqgMass σ m : ℝ) : ℂ)
      * Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ))) (eqgCharProc σ t) := by
  refine Summable.hasSum (Summable.of_norm ?_)
  refine (summable_eqgMass σ).congr fun m => ?_
  rw [norm_mul, norm_eqgPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (eqgMass_nonneg σ m)]

theorem eqgCharProc_eq_inner (σ : EulerSigma) (t : ℝ) :
    eqgCharProc σ t = (inner ℂ (eqgOmega σ) (eqgOrbit σ t) : ℂ) := by
  rw [lp.inner_eq_tsum, eqgCharProc]
  refine tsum_congr fun m => ?_
  rw [RCLike.inner_apply, eqgOmega_apply, eqgOrbit_apply, Complex.conj_ofReal]
  have hsq : ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ) * ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ)
      = ((eqgMass σ m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (eqgMass_nonneg σ m)]
  rw [← hsq]
  ring

/-! ## Recurrence of the orbit -/

theorem eqgOrbit_sub_eqgOmega_apply (σ : EulerSigma) (t : ℝ) (m : ℕ) :
    ((eqgOrbit σ t - eqgOmega σ : QGammaSpace) : ℕ → ℂ) m
      = (Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)) - 1)
        * ((Real.sqrt (eqgMass σ m) : ℝ) : ℂ) := by
  rw [lp.coeFn_sub]
  show (eqgOrbit σ t : ℕ → ℂ) m - (eqgOmega σ : ℕ → ℂ) m = _
  rw [eqgOrbit_apply, eqgOmega_apply]
  ring

theorem norm_eqgOrbit_sub_eqgOmega_sq (σ : EulerSigma) (t : ℝ) :
    ‖eqgOrbit σ t - eqgOmega σ‖ ^ 2
      = ∑' m : ℕ, eqgMass σ m
        * ‖Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)) - 1‖ ^ 2 := by
  rw [norm_sq_lp]
  refine tsum_congr fun m => ?_
  rw [eqgOrbit_sub_eqgOmega_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (eqgMass_nonneg σ m)]
  ring

theorem eqgOrbitDiff_le_four (σ : EulerSigma) (t : ℝ) (m : ℕ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)) - 1‖ ^ 2 ≤ 4 := by
  have hb : ‖Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)) - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_eqgPhase, norm_one]
    norm_num
  nlinarith [norm_nonneg (Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)) - 1)]

theorem eqgOrbitDiff_summable (σ : EulerSigma) (t : ℝ) :
    Summable (fun m : ℕ => eqgMass σ m
      * ‖Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)) - 1‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (eqgMass_nonneg σ m) (sq_nonneg _)) (fun m => ?_)
    ((summable_eqgMass σ).mul_left 4)
  have h4 := eqgOrbitDiff_le_four σ t m
  have hw := eqgMass_nonneg σ m
  nlinarith

/-- **Theorem 8.1, the recurrence clause.**  At arbitrarily late integer times the orbit vector
returns to the cyclic vector. -/
theorem exists_eqgOrbit_near_eqgOmega (σ : EulerSigma) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ ‖eqgOrbit σ (m : ℝ) - eqgOmega σ‖ < ε := by
  classical
  have hsum := eqgMass_hasSum_one σ
  have hsummable := summable_eqgMass σ
  have htail : Filter.Tendsto (fun N : ℕ => ∑' k : ℕ, eqgMass σ (k + N)) Filter.atTop
      (𝓝 0) := tendsto_sum_nat_add (eqgMass σ)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' k : ℕ, eqgMass σ (k + (N + 1)) < ε ^ 2 / 8 := by
    have hpos : (0 : ℝ) < ε ^ 2 / 8 := by positivity
    obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (htail.eventually (gt_mem_nhds hpos))
    exact ⟨i₀, hi₀ (i₀ + 1) (by omega)⟩
  set g : Fin (N + 1) → Circle := fun i => Circle.exp (eqgObservable σ (i : ℕ)) with hg
  set s : Set Circle := {c : Circle | ‖(c : ℂ) - 1‖ < ε / 2} with hs
  have hsopen : IsOpen s := by
    have hcont : Continuous fun c : Circle => ‖(c : ℂ) - 1‖ := by fun_prop
    exact isOpen_lt hcont continuous_const
  have hsmem : s ∈ 𝓝 (1 : Circle) := by
    refine hsopen.mem_nhds ?_
    show ‖((1 : Circle) : ℂ) - 1‖ < ε / 2
    simp
    linarith
  have hU : Set.pi Set.univ (fun _ : Fin (N + 1) => s) ∈ 𝓝 (1 : Fin (N + 1) → Circle) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => hsmem
  obtain ⟨m, hm, hmem⟩ := exists_pow_mem_of_compactSpace g hU M
  refine ⟨m, hm, ?_⟩
  have hhead : ∀ k : ℕ, ∀ hk : k < N + 1,
      ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((eqgObservable σ k : ℝ) : ℂ)) - 1‖ < ε / 2 := by
    intro k hk
    have hj : (g ^ m) ⟨k, hk⟩ ∈ s := hmem ⟨k, hk⟩ (Set.mem_univ _)
    rw [hs, Set.mem_setOf_eq] at hj
    have hval : (((g ^ m) ⟨k, hk⟩ : Circle) : ℂ)
        = Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((eqgObservable σ k : ℝ) : ℂ)) := by
      show (((g ⟨k, hk⟩) ^ m : Circle) : ℂ) = _
      rw [Circle.coe_pow, hg]
      simp only [Circle.coe_exp]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [hval] at hj
  have hnormsq : ‖eqgOrbit σ (m : ℝ) - eqgOmega σ‖ ^ 2 < ε ^ 2 := by
    rw [norm_eqgOrbit_sub_eqgOmega_sq]
    have hsplit := (eqgOrbitDiff_summable σ (m : ℝ)).sum_add_tsum_nat_add (N + 1)
    rw [← hsplit]
    have hhead_bound : ∑ i ∈ Finset.range (N + 1), eqgMass σ i
        * ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((eqgObservable σ i : ℝ) : ℂ)) - 1‖ ^ 2
        ≤ (ε / 2) ^ 2 := by
      have hle : ∀ i ∈ Finset.range (N + 1), eqgMass σ i
          * ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((eqgObservable σ i : ℝ) : ℂ)) - 1‖ ^ 2
          ≤ eqgMass σ i * (ε / 2) ^ 2 := by
        intro i hi
        have hilt : i < N + 1 := Finset.mem_range.mp hi
        have hb := hhead i hilt
        have hnn := norm_nonneg
          (Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((eqgObservable σ i : ℝ) : ℂ)) - 1)
        have hw := eqgMass_nonneg σ i
        have hsq : ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ)
            * ((eqgObservable σ i : ℝ) : ℂ)) - 1‖ ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hsq hw
      refine le_trans (Finset.sum_le_sum hle) ?_
      rw [← Finset.sum_mul]
      have hmass : ∑ i ∈ Finset.range (N + 1), eqgMass σ i ≤ 1 :=
        sum_le_hasSum _ (fun i _ => eqgMass_nonneg σ i) hsum
      nlinarith [sq_nonneg (ε / 2)]
    have htail_bound : ∑' i : ℕ, eqgMass σ (i + (N + 1))
        * ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ)
          * ((eqgObservable σ (i + (N + 1)) : ℝ) : ℂ)) - 1‖ ^ 2
        ≤ 4 * ∑' i : ℕ, eqgMass σ (i + (N + 1)) := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => ?_) ?_ ?_
      · have h4 := eqgOrbitDiff_le_four σ (m : ℝ) (i + (N + 1))
        have hw := eqgMass_nonneg σ (i + (N + 1))
        nlinarith
      · exact ((eqgOrbitDiff_summable σ (m : ℝ)).comp_injective (add_left_injective (N + 1)))
      · exact (hsummable.comp_injective (add_left_injective (N + 1))).mul_left 4
    rw [show (ε / 2) ^ 2 = ε ^ 2 / 4 by ring] at hhead_bound
    have hεsq : 0 < ε ^ 2 := by positivity
    linarith [hhead_bound, htail_bound, hN, hεsq]
  have hnn : 0 ≤ ‖eqgOrbit σ (m : ℝ) - eqgOmega σ‖ := norm_nonneg _
  nlinarith [hnormsq, hnn, hε]

/-! ## The characteristic function is the response at an imaginary argument -/

/-- **Equation (EQG.9), characteristic form.**  `C_σ(t) = F_σ(it)`. -/
theorem eqgCharProc_eq_response (σ : EulerSigma) (t : ℝ) :
    eqgCharProc σ t = eqgResponse σ (Complex.I * (t : ℂ)) := by
  set s : ℂ := Complex.I * (t : ℂ) with hs
  have hre : 1 < (eqgExponent σ s).re := by
    have hval : (eqgExponent σ s).re = σ.val := by
      rw [eqgExponent, hs]
      simp
    rw [hval]
    exact σ.one_lt
  have hsum : HasSum (eqgTerm σ (eqgExponent σ s)) (eqgDirichlet σ (eqgExponent σ s)) :=
    (summable_eqgTerm σ hre).hasSum
  have h2 := (hsum.mul_left (((eqgConst σ : ℝ) : ℂ))).mul_left (riemannZeta (σ.val : ℂ) ^ s)
  have hterm : ∀ m : ℕ,
      riemannZeta (σ.val : ℂ) ^ s * (((eqgConst σ : ℝ) : ℂ) * eqgTerm σ (eqgExponent σ s) m)
        = ((eqgMass σ m : ℝ) : ℂ)
          * Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · rw [eqgTerm_zero, eqgMass, eqgWeight_zero]
      simp
    · rw [eqgTerm_eqgExponent, eqgMass, Complex.ofReal_mul,
        show Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)
          = s * ((eqgObservable σ m : ℝ) : ℂ) from rfl,
        exp_eqgObservable σ s hm]
      ring
  have h3 : HasSum (fun m : ℕ => ((eqgMass σ m : ℝ) : ℂ)
      * Complex.exp (Complex.I * (t : ℂ) * ((eqgObservable σ m : ℝ) : ℂ)))
      (riemannZeta (σ.val : ℂ) ^ s
        * (((eqgConst σ : ℝ) : ℂ) * eqgDirichlet σ (eqgExponent σ s))) := by
    refine h2.congr_fun fun m => ?_
    exact (hterm m).symm
  rw [eqgResponse]
  exact ((eqgCharProc_hasSum σ t).unique h3)

end

end GaloisForLFunctions.HTGeometry
