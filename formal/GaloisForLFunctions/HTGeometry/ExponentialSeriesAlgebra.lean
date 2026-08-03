import GaloisForLFunctions.HTGeometry.ComplexExponentialSeriesCarrier

/-!
# Exponential series are closed under products and derivatives

A product of two absolutely convergent exponential series is an exponential series indexed by the
pairs, with the frequencies added; a derivative is an exponential series with the same frequencies
and the amplitudes multiplied by `i omega`.

Normal summability survives the derivative because `|x| <= exp |x|` absorbs the extra factor into
the next exponential weight.  So every monomial in the jets of a carrier is again an exponential
series, which is what a Bohr-coefficient argument needs.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

variable {ι κ : Type*}

/-! ## Products -/

theorem expSeriesCarrier_mul {b : ι → ℂ} {c : κ → ℂ} (omega : ι → ℝ) (nu : κ → ℝ)
    (hb : Summable fun i => ‖b i‖) (hc : Summable fun j => ‖c j‖) (t : ℝ) :
    expSeriesCarrier b omega t * expSeriesCarrier c nu t
      = expSeriesCarrier (fun p : ι × κ => b p.1 * c p.2)
        (fun p : ι × κ => omega p.1 + nu p.2) t := by
  have hbn : Summable fun i => ‖b i * expChar (omega i) t‖ := by
    simpa [norm_mul] using hb
  have hcn : Summable fun j => ‖c j * expChar (nu j) t‖ := by
    simpa [norm_mul] using hc
  rw [expSeriesCarrier, expSeriesCarrier, tsum_mul_tsum_of_summable_norm hbn hcn,
    expSeriesCarrier]
  refine tsum_congr fun p => ?_
  rw [← expChar_add]
  ring

theorem summable_norm_mul {b : ι → ℂ} {c : κ → ℂ}
    (hb : Summable fun i => ‖b i‖) (hc : Summable fun j => ‖c j‖) :
    Summable fun p : ι × κ => ‖b p.1 * c p.2‖ :=
  hb.mul_norm hc

/-! ## Derivatives -/

theorem abs_le_exp_abs (x : ℝ) : |x| ≤ Real.exp |x| :=
  le_trans (by linarith) (Real.add_one_le_exp |x|)

/-- **Normal summability survives differentiation.** -/
theorem ExpSeriesNormallySummable.deriv {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) :
    ExpSeriesNormallySummable (fun i => a i * (Complex.I * (omega i : ℂ))) omega := by
  intro R
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (h (R + 1))
  have hnorm : ‖a i * (Complex.I * (omega i : ℂ))‖ = ‖a i‖ * |omega i| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have habs : |omega i| ≤ Real.exp |omega i| := abs_le_exp_abs _
  have hstep : Real.exp (R * |omega i|) * |omega i|
      ≤ Real.exp (R * |omega i|) * Real.exp |omega i| :=
    mul_le_mul_of_nonneg_left habs (Real.exp_nonneg _)
  have hcomb : Real.exp (R * |omega i|) * Real.exp |omega i|
      = Real.exp ((R + 1) * |omega i|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc ‖a i‖ * |omega i| * Real.exp (R * |omega i|)
      = ‖a i‖ * (Real.exp (R * |omega i|) * |omega i|) := by ring
    _ ≤ ‖a i‖ * (Real.exp (R * |omega i|) * Real.exp |omega i|) :=
        mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
    _ = ‖a i‖ * Real.exp ((R + 1) * |omega i|) := by rw [hcomb]

theorem hasDerivAt_cexpChar (omega : ℝ) (z : ℂ) :
    HasDerivAt (cexpChar omega) (Complex.I * (omega : ℂ) * cexpChar omega z) z := by
  have hlin : HasDerivAt (fun w : ℂ => Complex.I * (omega : ℂ) * w)
      (Complex.I * (omega : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul (Complex.I * (omega : ℂ))
  have hd : HasDerivAt (cexpChar omega)
      (Complex.exp (Complex.I * (omega : ℂ) * z) * (Complex.I * (omega : ℂ))) z := hlin.cexp
  have hval : Complex.exp (Complex.I * (omega : ℂ) * z) * (Complex.I * (omega : ℂ))
      = Complex.I * (omega : ℂ) * cexpChar omega z := by
    rw [cexpChar]
    ring
  rwa [hval] at hd

theorem deriv_cexpChar (omega : ℝ) (z : ℂ) :
    deriv (cexpChar omega) z = Complex.I * (omega : ℂ) * cexpChar omega z :=
  (hasDerivAt_cexpChar omega z).deriv

/-- **The derivative of an exponential series is the exponential series of the scaled
amplitudes.**  Termwise differentiation is legitimate because the partial sums converge locally
uniformly. -/
theorem deriv_cexpSeriesCarrier {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) :
    deriv (cexpSeriesCarrier a omega)
      = cexpSeriesCarrier (fun i => a i * (Complex.I * (omega i : ℂ))) omega := by
  funext z
  have hpartial : ∀ S : Finset ι, HasDerivAt (fun w => ∑ i ∈ S, a i * cexpChar (omega i) w)
      (∑ i ∈ S, a i * (Complex.I * (omega i : ℂ)) * cexpChar (omega i) z) z := by
    intro S
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h1 := (hasDerivAt_cexpChar (omega i) z).const_mul (a i)
    have hval : a i * (Complex.I * (omega i : ℂ) * cexpChar (omega i) z)
        = a i * (Complex.I * (omega i : ℂ)) * cexpChar (omega i) z := by ring
    rwa [hval] at h1
  have hdiff : ∀ᶠ S : Finset ι in atTop, DifferentiableOn ℂ
      (fun w => ∑ i ∈ S, a i * cexpChar (omega i) w) Set.univ := by
    refine Filter.Eventually.of_forall fun S w _ => ?_
    have hd : HasDerivAt (fun w => ∑ i ∈ S, a i * cexpChar (omega i) w)
        (∑ i ∈ S, a i * (Complex.I * (omega i : ℂ) * cexpChar (omega i) w)) w := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      exact (hasDerivAt_cexpChar (omega i) w).const_mul (a i)
    exact hd.differentiableAt.differentiableWithinAt
  have hderiv := (tendstoLocallyUniformly_cexpSeries h).deriv hdiff isOpen_univ
  have h1 := hderiv.tendsto_at (Set.mem_univ z)
  have hseq : (fun S : Finset ι => (deriv ∘ fun (S : Finset ι) (w : ℂ) =>
        ∑ i ∈ S, a i * cexpChar (omega i) w) S z)
      = fun S : Finset ι => ∑ i ∈ S, a i * (Complex.I * (omega i : ℂ)) * cexpChar (omega i) z := by
    funext S
    exact (hpartial S).deriv
  rw [hseq] at h1
  have h2 : Filter.Tendsto (fun S : Finset ι =>
      ∑ i ∈ S, a i * (Complex.I * (omega i : ℂ)) * cexpChar (omega i) z) atTop
      (nhds (cexpSeriesCarrier (fun i => a i * (Complex.I * (omega i : ℂ))) omega z)) :=
    (summable_cexpSeries h.deriv z).hasSum
  exact tendsto_nhds_unique h1 h2

/-- **Every jet of an exponential series is an exponential series.**  The `k`-th derivative has the
same frequencies and the amplitudes multiplied by `(i omega)^k`. -/
theorem iteratedDeriv_cexpSeriesCarrier : ∀ (k : ℕ) {a : ι → ℂ} {omega : ι → ℝ},
    ExpSeriesNormallySummable a omega →
    iteratedDeriv k (cexpSeriesCarrier a omega)
      = cexpSeriesCarrier (fun i => a i * (Complex.I * (omega i : ℂ)) ^ k) omega := by
  intro k
  induction k with
  | zero =>
      intro a omega _
      funext z
      rw [iteratedDeriv_zero, cexpSeriesCarrier, cexpSeriesCarrier]
      refine tsum_congr fun i => ?_
      ring
  | succ k ih =>
      intro a omega h
      rw [iteratedDeriv_succ', deriv_cexpSeriesCarrier h, ih h.deriv]
      funext z
      rw [cexpSeriesCarrier, cexpSeriesCarrier]
      refine tsum_congr fun i => ?_
      ring

/-- The jets of an exponential series are normally summable. -/
theorem ExpSeriesNormallySummable.iteratedDeriv {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) : ∀ k : ℕ,
    ExpSeriesNormallySummable (fun i => a i * (Complex.I * (omega i : ℂ)) ^ k) omega := by
  intro k
  induction k generalizing a with
  | zero =>
      have hval : (fun i => a i * (Complex.I * (omega i : ℂ)) ^ 0) = a := by
        funext i
        ring
      rw [hval]
      exact h
  | succ k ih =>
      have hval : (fun i => a i * (Complex.I * (omega i : ℂ)) ^ (k + 1))
          = fun i => (a i * (Complex.I * (omega i : ℂ))) * (Complex.I * (omega i : ℂ)) ^ k := by
        funext i
        ring
      rw [hval]
      exact ih h.deriv

/-! ## Finite products -/

theorem consEquiv_apply {m : ℕ} (p : ι × (Fin m → ι)) (j : Fin (m + 1)) :
    (Fin.consEquiv (fun _ : Fin (m + 1) => ι) p) j
      = Fin.cons (α := fun _ : Fin (m + 1) => ι) p.1 p.2 j := rfl

theorem expChar_zero (t : ℝ) : expChar 0 t = 1 := by
  simp [expChar]

set_option maxHeartbeats 1000000 in
theorem summable_norm_prod_expSeries : ∀ (m : ℕ) (b : Fin m → ι → ℂ),
    (∀ j, Summable fun i => ‖b j i‖) →
    Summable fun n : Fin m → ι => ‖∏ j, b j (n j)‖ := by
  intro m
  induction m with
  | zero =>
      intro b _
      exact Summable.of_finite
  | succ m ih =>
      intro b hb
      have hrest : Summable fun n : Fin m → ι => ‖∏ j, b j.succ (n j)‖ :=
        ih (fun j => b j.succ) (fun j => hb j.succ)
      have hpair : Summable fun p : ι × (Fin m → ι) => ‖b 0 p.1 * ∏ j, b j.succ (p.2 j)‖ := by
        have hmul : Summable fun p : ι × (Fin m → ι) =>
            ‖b 0 p.1‖ * ‖∏ j, b j.succ (p.2 j)‖ :=
          Summable.mul_of_nonneg (hb 0) hrest (fun i => norm_nonneg _) (fun n => norm_nonneg _)
        refine hmul.congr fun p => ?_
        rw [norm_mul]
      have hiff := (Fin.consEquiv (fun _ : Fin (m + 1) => ι)).summable_iff
        (f := fun n : Fin (m + 1) → ι => ‖∏ j, b j (n j)‖)
      rw [← hiff]
      refine hpair.congr fun p => ?_
      show ‖b 0 p.1 * ∏ j, b j.succ (p.2 j)‖
        = ‖∏ j, b j ((Fin.consEquiv (fun _ : Fin (m + 1) => ι) p) j)‖
      simp only [consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **A finite product of exponential series is an exponential series indexed by tuples.**  The
amplitudes multiply and the frequencies add. -/
theorem prod_expSeriesCarrier : ∀ (m : ℕ) (b : Fin m → ι → ℂ) (omega : ι → ℝ),
    (∀ j, Summable fun i => ‖b j i‖) → ∀ t : ℝ,
    ∏ j, expSeriesCarrier (b j) omega t
      = expSeriesCarrier (fun n : Fin m → ι => ∏ j, b j (n j))
        (fun n : Fin m → ι => ∑ j, omega (n j)) t := by
  intro m
  induction m with
  | zero =>
      intro b omega _ t
      rw [Fin.prod_univ_zero, expSeriesCarrier,
        tsum_eq_single (default : Fin 0 → ι) (fun n hn => absurd (Subsingleton.elim n default) hn),
        Fin.prod_univ_zero, Fin.sum_univ_zero, expChar_zero]
      simp
  | succ m ih =>
      intro b omega hb t
      have hrest := ih (fun j => b j.succ) omega (fun j => hb j.succ) t
      have hprodsum := summable_norm_prod_expSeries m (fun j => b j.succ) (fun j => hb j.succ)
      rw [Fin.prod_univ_succ, hrest,
        expSeriesCarrier_mul omega (fun n : Fin m → ι => ∑ j, omega (n j)) (hb 0) hprodsum t,
        expSeriesCarrier, expSeriesCarrier]
      rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ι)).tsum_eq
        (fun n : Fin (m + 1) → ι => (∏ j, b j (n j)) * expChar (∑ j, omega (n j)) t)]
      refine tsum_congr fun p => ?_
      have hprod : ∏ j, b j ((Fin.consEquiv (fun _ : Fin (m + 1) => ι) p) j)
          = b 0 p.1 * ∏ j, b j.succ (p.2 j) := by
        simp only [consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hfreq : ∑ j, omega ((Fin.consEquiv (fun _ : Fin (m + 1) => ι) p) j)
          = omega p.1 + ∑ j, omega (p.2 j) := by
        simp only [consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [hprod, hfreq]

end

end GaloisForLFunctions
