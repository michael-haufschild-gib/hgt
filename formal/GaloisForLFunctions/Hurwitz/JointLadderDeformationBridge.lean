import GaloisForLFunctions.Hurwitz.JointPowerOrbit

open Complex HurwitzZetaShift HurwitzN2Tail HurwitzN2HZeta HurwitzSpine HurwitzOrbit

namespace HurwitzJointLadder

open HurwitzLadder

variable {ι : Type*} {N : ℕ}

noncomputable def jointRelA (s : ι → ℂ) (M : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) (a : ℂ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom a)
    (fun jk => dzeta (s jk.1) M (c jk.1) (jk.2 : ℕ) a) P

noncomputable def jointRelZ (s : ι → ℂ) (M : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) (n : Fin (M + 1)) (z : ℂ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom (-((n : ℕ) : ℂ) + Complex.exp z))
    (fun jk => dmodel (s jk.1) M (c jk.1) n (jk.2 : ℕ) z) P

noncomputable def jointMove (s : ι → ℂ) {M : ℕ}
    (c : ι → Fin (M + 1) → ℂ) (n : Fin (M + 1)) : ι → Fin (M + 1) → ℂ :=
  fun j => Function.update (c j) n (monoScalar (s j) * c j n)

theorem jointRelA_eq_jointRelZ {s : ι → ℂ} (hs : ∀ j, 1 < (s j).re) {M : ℕ}
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) (n : Fin (M + 1))
    {z : ℂ} (h0 : 0 < z.im) (hπ : z.im < Real.pi) :
    jointRelA s M P c (-((n : ℕ) : ℂ) + Complex.exp z) = jointRelZ s M P c n z := by
  have hg : (fun jk : ι × Fin (N + 1) =>
      dzeta (s jk.1) M (c jk.1) (jk.2 : ℕ) (-((n : ℕ) : ℂ) + Complex.exp z)) =
      fun jk => dmodel (s jk.1) M (c jk.1) n (jk.2 : ℕ) z := by
    funext jk
    exact dzeta_eq_dmodel (hs jk.1) (c jk.1) n (jk.2 : ℕ) h0 hπ
  rw [jointRelA, jointRelZ, hg]

theorem jointRelZ_shift (s : ι → ℂ) {M : ℕ}
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) (n : Fin (M + 1)) (z : ℂ) :
    jointRelZ s M P c n (z + 2 * (Real.pi : ℂ) * Complex.I) =
      jointRelZ s M P (jointMove s c n) n z := by
  have harg : -((n : ℕ) : ℂ) + Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I) =
      -((n : ℕ) : ℂ) + Complex.exp z := by
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hg : (fun jk : ι × Fin (N + 1) =>
      dmodel (s jk.1) M (c jk.1) n (jk.2 : ℕ)
        (z + 2 * (Real.pi : ℂ) * Complex.I)) =
      fun jk => dmodel (s jk.1) M ((jointMove s c n) jk.1) n (jk.2 : ℕ) z := by
    funext jk
    exact dmodel_shift (s jk.1) (c jk.1) n (jk.2 : ℕ) z
  rw [jointRelZ, jointRelZ, harg, hg]

theorem jointRelZ_differentiableOn {s : ι → ℂ} (hs : ∀ j, 1 < (s j).re) {M : ℕ}
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) (n : Fin (M + 1)) :
    DifferentiableOn ℂ (jointRelZ s M P c n) HurwitzN2BlockAnalytic.region := by
  have hexpand : jointRelZ s M P c n = fun z =>
      ∑ d ∈ P.support, (MvPolynomial.coeff d P).eval (-((n : ℕ) : ℂ) + Complex.exp z) *
        ∏ jk ∈ d.support, (dmodel (s jk.1) M (c jk.1) n (jk.2 : ℕ) z) ^ (d jk) := by
    funext z
    rw [jointRelZ, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Polynomial.coe_evalRingHom]
  rw [hexpand]
  apply DifferentiableOn.fun_sum
  intro d _
  apply DifferentiableOn.mul
  · have : DifferentiableOn ℂ
        (fun z => (MvPolynomial.coeff d P).eval (-((n : ℕ) : ℂ) + Complex.exp z))
        HurwitzN2BlockAnalytic.region := by fun_prop
    exact this
  · have hprod : DifferentiableOn ℂ
        (∏ jk ∈ d.support,
          fun z => (dmodel (s jk.1) M (c jk.1) n (jk.2 : ℕ) z) ^ (d jk))
        HurwitzN2BlockAnalytic.region := by
      apply DifferentiableOn.finsetProd
      intro jk _
      exact (dmodel_differentiableOn (hs jk.1) (c jk.1) n (jk.2 : ℕ)).pow _
    refine DifferentiableOn.congr hprod ?_
    intro z _
    rw [Finset.prod_apply]

theorem jointRelA_differentiableOn {s : ι → ℂ} (hs : ∀ j, 1 < (s j).re) {M : ℕ}
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) :
    DifferentiableOn ℂ (jointRelA s M P c) UHP := by
  have hexpand : jointRelA s M P c = fun a =>
      ∑ d ∈ P.support, (MvPolynomial.coeff d P).eval a *
        ∏ jk ∈ d.support, (dzeta (s jk.1) M (c jk.1) (jk.2 : ℕ) a) ^ (d jk) := by
    funext a
    rw [jointRelA, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Polynomial.coe_evalRingHom]
  rw [hexpand]
  apply DifferentiableOn.fun_sum
  intro d _
  apply DifferentiableOn.mul
  · exact (Polynomial.differentiable _).differentiableOn
  · have hprod : DifferentiableOn ℂ
        (∏ jk ∈ d.support,
          fun a => (dzeta (s jk.1) M (c jk.1) (jk.2 : ℕ) a) ^ (d jk)) UHP := by
      apply DifferentiableOn.finsetProd
      intro jk _
      exact (dzeta_differentiableOn (hs jk.1) M (c jk.1) (jk.2 : ℕ)).pow _
    refine DifferentiableOn.congr hprod ?_
    intro a _
    rw [Finset.prod_apply]

theorem jointRelZ_zero_of_upper {s : ι → ℂ} (hs : ∀ j, 1 < (s j).re) {M : ℕ}
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) (n : Fin (M + 1))
    (hupper : ∀ z : ℂ, z ∈ HurwitzN2BlockAnalytic.region → 0 < z.im → z.im < Real.pi →
      jointRelZ s M P c n z = 0) :
    ∀ z ∈ HurwitzN2BlockAnalytic.region, jointRelZ s M P c n z = 0 := by
  have hFan : AnalyticOnNhd ℂ (jointRelZ s M P c n) HurwitzN2BlockAnalytic.region :=
    (jointRelZ_differentiableOn hs P c n).analyticOnNhd HurwitzN2BlockAnalytic.isOpen_region
  have hpre : IsPreconnected HurwitzN2BlockAnalytic.region :=
    (convex_halfSpace_re_lt (-Real.log 2)).isPreconnected
  set z₀ : ℂ := ⟨-Real.log 2 - 1, Real.pi / 2⟩ with hz₀def
  have hz₀mem : z₀ ∈ HurwitzN2BlockAnalytic.region := by
    show z₀.re < -Real.log 2
    rw [hz₀def]
    norm_num
  have hWopen : IsOpen (HurwitzN2BlockAnalytic.region
      ∩ {z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < Real.pi}) :=
    (HurwitzN2BlockAnalytic.isOpen_region.inter
      (isOpen_lt continuous_const Complex.continuous_im)).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hz₀W : z₀ ∈ HurwitzN2BlockAnalytic.region
      ∩ {z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < Real.pi} := by
    refine ⟨⟨hz₀mem, ?_⟩, ?_⟩
    · show (0 : ℝ) < z₀.im
      rw [hz₀def]
      simpa using Real.pi_pos
    · show z₀.im < Real.pi
      rw [hz₀def]
      show Real.pi / 2 < Real.pi
      linarith [Real.pi_pos]
  have hev : jointRelZ s M P c n =ᶠ[nhds z₀] 0 :=
    Filter.eventuallyEq_of_mem (hWopen.mem_nhds hz₀W)
      (fun z hz => hupper z hz.1.1 hz.1.2 hz.2)
  have hzero : Set.EqOn (jointRelZ s M P c n) 0 HurwitzN2BlockAnalytic.region :=
    hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz₀mem hev
  intro z hz
  exact hzero hz

theorem jointRelA_move {s : ι → ℂ} (hs : ∀ j, 1 < (s j).re) {M : ℕ}
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (c : ι → Fin (M + 1) → ℂ) (n : Fin (M + 1))
    (h : ∀ a : ℂ, 0 < a.im → jointRelA s M P c a = 0) :
    ∀ a : ℂ, 0 < a.im → jointRelA s M P (jointMove s c n) a = 0 := by
  have hupper : ∀ z : ℂ, z ∈ HurwitzN2BlockAnalytic.region → 0 < z.im → z.im < Real.pi →
      jointRelZ s M P c n z = 0 := by
    intro z _ h0 hπ
    rw [← jointRelA_eq_jointRelZ hs P c n h0 hπ]
    apply h
    show 0 < (-((n : ℕ) : ℂ) + Complex.exp z).im
    have him : (-((n : ℕ) : ℂ) + Complex.exp z).im = (Complex.exp z).im := by simp
    rw [him, Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  have hregion := jointRelZ_zero_of_upper hs P c n hupper
  have hc' : ∀ z ∈ HurwitzN2BlockAnalytic.region,
      jointRelZ s M P (jointMove s c n) n z = 0 := by
    intro z hz
    have hzshift : z + 2 * (Real.pi : ℂ) * Complex.I ∈ HurwitzN2BlockAnalytic.region := by
      show (z + 2 * (Real.pi : ℂ) * Complex.I).re < -Real.log 2
      have hre : (z + 2 * (Real.pi : ℂ) * Complex.I).re = z.re := by simp
      rw [hre]
      exact hz
    have h0 := hregion _ hzshift
    rwa [jointRelZ_shift] at h0
  have hpatch : ∀ a : ℂ, 0 < (a + ((n : ℕ) : ℂ)).im → ‖a + ((n : ℕ) : ℂ)‖ < 1 / 2 →
      jointRelA s M P (jointMove s c n) a = 0 := by
    intro a him hnorm
    set x : ℂ := a + ((n : ℕ) : ℂ) with hx
    have hxne : x ≠ 0 := by
      intro hh
      rw [hh] at him
      simp at him
    set z : ℂ := Complex.log x with hz
    have hexpz : Complex.exp z = x := Complex.exp_log hxne
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hzre : z ∈ HurwitzN2BlockAnalytic.region := by
      show z.re < -Real.log 2
      rw [hz, Complex.log_re]
      have h1 : Real.log ‖x‖ < Real.log (1 / 2) := Real.log_lt_log hxpos hnorm
      have h2 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
        rw [show (1 / 2 : ℝ) = 2⁻¹ from by norm_num, Real.log_inv]
      linarith
    have hsin : 0 < Real.sin x.arg := by
      rw [Complex.sin_arg]
      exact div_pos him hxpos
    have hargpos : 0 < x.arg := by
      rcases lt_trichotomy x.arg 0 with hlt | heq | hpos
      · have := Real.sin_neg_of_neg_of_neg_pi_lt hlt (Complex.neg_pi_lt_arg x)
        linarith
      · rw [heq, Real.sin_zero] at hsin
        exact absurd hsin (lt_irrefl 0)
      · exact hpos
    have hargpi : x.arg < Real.pi := by
      rcases lt_or_eq_of_le (Complex.arg_le_pi x) with hlt | heq
      · exact hlt
      · rw [heq, Real.sin_pi] at hsin
        exact absurd hsin (lt_irrefl 0)
    have h0z : 0 < z.im := by rw [hz, Complex.log_im]; exact hargpos
    have hπz : z.im < Real.pi := by rw [hz, Complex.log_im]; exact hargpi
    have ha_eq : a = -((n : ℕ) : ℂ) + Complex.exp z := by
      rw [hexpz, hx]
      ring
    rw [ha_eq, jointRelA_eq_jointRelZ hs P _ n h0z hπz]
    exact hc' z hzre
  have hAn : AnalyticOnNhd ℂ (jointRelA s M P (jointMove s c n)) UHP :=
    (jointRelA_differentiableOn hs P _).analyticOnNhd isOpen_UHP
  set a₀ : ℂ := -((n : ℕ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * Complex.I with ha₀
  have ha₀x : a₀ + ((n : ℕ) : ℂ) = ((1 / 4 : ℝ) : ℂ) * Complex.I := by rw [ha₀]; ring
  have ha₀mem : a₀ ∈ UHP := by
    show 0 < a₀.im
    have : a₀.im = (a₀ + ((n : ℕ) : ℂ)).im := by simp
    rw [this, ha₀x]
    simp
  have hOopen : IsOpen {a : ℂ | 0 < (a + ((n : ℕ) : ℂ)).im ∧
      ‖a + ((n : ℕ) : ℂ)‖ < 1 / 2} := by
    apply IsOpen.inter
    · have hcont : Continuous fun a : ℂ => (a + ((n : ℕ) : ℂ)).im :=
        Complex.continuous_im.comp (continuous_id.add continuous_const)
      exact isOpen_lt continuous_const hcont
    · have hcont : Continuous fun a : ℂ => ‖a + ((n : ℕ) : ℂ)‖ :=
        (continuous_id.add continuous_const).norm
      exact isOpen_lt hcont continuous_const
  have ha₀O : a₀ ∈ {a : ℂ | 0 < (a + ((n : ℕ) : ℂ)).im ∧
      ‖a + ((n : ℕ) : ℂ)‖ < 1 / 2} := by
    constructor
    · rw [ha₀x]
      simp
    · rw [ha₀x, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      rw [Real.norm_eq_abs]
      norm_num
  have hev : jointRelA s M P (jointMove s c n) =ᶠ[nhds a₀] 0 :=
    Filter.eventuallyEq_of_mem (hOopen.mem_nhds ha₀O) (fun a ha => hpatch a ha.1 ha.2)
  have hzero := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_UHP
    ha₀mem hev
  intro a ha
  exact hzero ha

theorem jointRelA_grid {s : ι → ℂ} (hs : ∀ j, 1 < (s j).re) {M : ℕ}
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (h1 : ∀ a : ℂ, 0 < a.im → jointRelA s M P (fun _ _ => 1) a = 0) :
    ∀ m : Fin (M + 1) → ℕ, ∀ a : ℂ, 0 < a.im →
      jointRelA s M P (fun j n => monoScalar (s j) ^ m n) a = 0 := by
  suffices H : ∀ K : ℕ, ∀ m : Fin (M + 1) → ℕ, (∑ n, m n) = K →
      ∀ a : ℂ, 0 < a.im →
        jointRelA s M P (fun j n => monoScalar (s j) ^ m n) a = 0 by
    exact fun m => H (∑ n, m n) m rfl
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro m hm a ha
    by_cases h0 : ∀ n, m n = 0
    · have hc : (fun j : ι => fun n : Fin (M + 1) => monoScalar (s j) ^ m n) =
          fun _ _ => 1 := by
        funext j n
        rw [h0 n, pow_zero]
      rw [hc]
      exact h1 a ha
    · obtain ⟨n₀, hn₀⟩ := not_forall.mp h0
      have hn₀pos : 1 ≤ m n₀ := Nat.one_le_iff_ne_zero.mpr hn₀
      set m' : Fin (M + 1) → ℕ := Function.update m n₀ (m n₀ - 1) with hm'
      have hsum' : (∑ n, m' n) = K - 1 := by
        rw [hm', Finset.sum_update_of_mem (Finset.mem_univ n₀)]
        have hK : m n₀ + ∑ n ∈ Finset.univ \ {n₀}, m n = K := by
          rw [← Finset.erase_eq, Finset.add_sum_erase Finset.univ m (Finset.mem_univ n₀)]
          exact hm
        omega
      have hKpos : 1 ≤ K := by
        rw [← hm]
        calc 1 ≤ m n₀ := hn₀pos
          _ ≤ ∑ n, m n := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ n₀)
      have hprev : ∀ a : ℂ, 0 < a.im →
          jointRelA s M P (fun j n => monoScalar (s j) ^ m' n) a = 0 :=
        fun a' ha' => ih (K - 1) (by omega) m' hsum' a' ha'
      have hstep := jointRelA_move hs P (fun j n => monoScalar (s j) ^ m' n) n₀ hprev
      have hupd : jointMove s (fun j n => monoScalar (s j) ^ m' n) n₀ =
          fun j n => monoScalar (s j) ^ m n := by
        funext j n
        by_cases h : n = n₀
        · subst h
          rw [jointMove, Function.update_self, hm', Function.update_self]
          rw [show monoScalar (s j) * monoScalar (s j) ^ (m n - 1) =
              monoScalar (s j) ^ (m n - 1 + 1) from by rw [pow_succ]; ring]
          congr 1
          omega
        · rw [jointMove, Function.update_of_ne h, hm', Function.update_of_ne h]
      rw [← hupd]
      exact hstep a ha

end HurwitzJointLadder
