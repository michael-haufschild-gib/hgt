import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# The Xi divisor has reciprocal exponent three halves

The unconditional density estimate `N_Xi(r) = O(r log r)` implies the
summability of the Xi divisor with every reciprocal exponent strictly larger
than one.  This module extracts the exponent `3/2` in the form needed by the
rectangular CCM shifted-zeta carrier.  Multiplicity is retained exactly.
-/

open Complex Metric Function Filter MeromorphicOn

namespace RHTower

noncomputable section

/-- Base-four shell index.  The base is chosen so that the exponent `3/2`
turns the shell denominator into the integral power `8^k`. -/
noncomputable def xiShellFour (ρ : ℂ) : ℕ :=
  Nat.log 4 ⌊‖ρ - 2‖⌋₊

lemma four_pow_xiShellFour_le {ρ : ℂ} (h : (4 : ℝ) ≤ ‖ρ - 2‖) :
    (4 : ℝ) ^ xiShellFour ρ ≤ ‖ρ - 2‖ := by
  have h1 : (1 : ℝ) ≤ ‖ρ - 2‖ := by linarith
  have hm1 : 1 ≤ ⌊‖ρ - 2‖⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  calc
    (4 : ℝ) ^ xiShellFour ρ =
        ((4 ^ Nat.log 4 ⌊‖ρ - 2‖⌋₊ : ℕ) : ℝ) := by
          rw [xiShellFour]
          push_cast
          ring
    _ ≤ (⌊‖ρ - 2‖⌋₊ : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 4 (by omega)
    _ ≤ ‖ρ - 2‖ := Nat.floor_le (by positivity)

lemma norm_lt_four_pow_xiShellFour_succ (ρ : ℂ) :
    ‖ρ - 2‖ < (4 : ℝ) ^ (xiShellFour ρ + 1) := by
  have h1 : ‖ρ - 2‖ < (⌊‖ρ - 2‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnat : ⌊‖ρ - 2‖⌋₊ + 1 ≤ 4 ^ (xiShellFour ρ + 1) := by
    rw [xiShellFour]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (⌊‖ρ - 2‖⌋₊ : ℝ) + 1 ≤
      (4 : ℝ) ^ (xiShellFour ρ + 1) := by
    calc
      (⌊‖ρ - 2‖⌋₊ : ℝ) + 1 =
          ((⌊‖ρ - 2‖⌋₊ + 1 : ℕ) : ℝ) := by
            push_cast
            ring
      _ ≤ ((4 ^ (xiShellFour ρ + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      _ = (4 : ℝ) ^ (xiShellFour ρ + 1) := by
        push_cast
        ring
  linarith

/-- The real shell estimate for reciprocal exponent `3/2`. -/
lemma shell_term_bound_three_halves
    {a b d : ℝ} {s : ℕ} (hd : 0 ≤ d) (hb4 : 4 ≤ b)
    (hab : b / 2 ≤ a) (hbs : (4 : ℝ) ^ s ≤ b) :
    d / (a * Real.sqrt a) ≤ 4 * d * (1 / 8 : ℝ) ^ s := by
  have hbpos : 0 < b := by linarith
  have hapos : 0 < a := lt_of_lt_of_le (by linarith : 0 < b / 2) hab
  have hsqrtba : Real.sqrt (b / 2) ≤ Real.sqrt a :=
    Real.sqrt_le_sqrt hab
  have hdenom : (b / 2) * Real.sqrt (b / 2) ≤ a * Real.sqrt a := by
    gcongr
  have hsqrt_half : Real.sqrt b / 2 ≤ Real.sqrt (b / 2) := by
    have hb0 : 0 ≤ b := hbpos.le
    have hbh0 : 0 ≤ b / 2 := by positivity
    have hsqb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb0
    have hsqbh : (Real.sqrt (b / 2)) ^ 2 = b / 2 := Real.sq_sqrt hbh0
    have hsqrtb0 := Real.sqrt_nonneg b
    have hsqrtbh0 := Real.sqrt_nonneg (b / 2)
    nlinarith
  have hdenom_b : b * Real.sqrt b / 4 ≤ a * Real.sqrt a := by
    calc
      b * Real.sqrt b / 4 = (b / 2) * (Real.sqrt b / 2) := by ring
      _ ≤ (b / 2) * Real.sqrt (b / 2) := by gcongr
      _ ≤ a * Real.sqrt a := hdenom
  have hsqrt_pow : Real.sqrt ((4 : ℝ) ^ s) = (2 : ℝ) ^ s := by
    have hsq : ((4 : ℝ) ^ s) = ((2 : ℝ) ^ s) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hsqrt_lower : (2 : ℝ) ^ s ≤ Real.sqrt b := by
    rw [← hsqrt_pow]
    exact Real.sqrt_le_sqrt hbs
  have hpows : (8 : ℝ) ^ s ≤ b * Real.sqrt b := by
    calc
      (8 : ℝ) ^ s = (4 : ℝ) ^ s * (2 : ℝ) ^ s := by
        rw [← mul_pow]
        norm_num
      _ ≤ b * Real.sqrt b := by gcongr
  have hdenom_pow : (8 : ℝ) ^ s / 4 ≤ a * Real.sqrt a :=
    le_trans (by linarith [hpows]) hdenom_b
  calc
    d / (a * Real.sqrt a) ≤ d / ((8 : ℝ) ^ s / 4) :=
      div_le_div_of_nonneg_left hd (by positivity) hdenom_pow
    _ = 4 * d * (1 / 8 : ℝ) ^ s := by
      rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num, inv_pow]
      field_simp

/-- The Xi divisor, counted with analytic multiplicity, is summable at
reciprocal exponent `3/2`. -/
theorem xi_zero_multiplicity_inv_three_halves_summable :
    Summable (fun ρ : XiDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖)) := by
  classical
  obtain ⟨C, hCpos, hN⟩ := xi_zeroCount_growth
  set D := MeromorphicOn.divisor xi Set.univ with hDdef
  set f : ↥D.support → ℝ := fun ρ =>
    ((D (ρ : ℂ) : ℝ)) / (‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖) with hfdef
  have hfnn : ∀ ρ : ↥D.support, 0 ≤ f ρ := by
    intro ρ
    apply div_nonneg _ (by positivity)
    exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
  set bnd : ℕ → ℝ := fun k =>
    (1 / 8 : ℝ) ^ k *
      (C * (1 + (4 : ℝ) ^ (k + 1)) * Real.log (2 + (4 : ℝ) ^ (k + 1)))
      with hbnddef
  have hbndnn : ∀ k, 0 ≤ bnd k := by
    intro k
    have hlog0 : 0 ≤ Real.log (2 + (4 : ℝ) ^ (k + 1)) :=
      Real.log_nonneg (by
        nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) (k + 1)])
    simp only [hbnddef]
    positivity
  have hbndsum : Summable bnd := by
    have hs1 : Summable (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one
        (R := ℝ) 1 (r := 1 / 2) (by rw [Real.norm_eq_abs]; norm_num)
      simpa using h
    have hs2 : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hdom : Summable (fun k : ℕ =>
        (5 * C * Real.log 4) * (((k : ℝ) + 2) * (1 / 2) ^ k)) := by
      apply Summable.mul_left
      have h := hs1.add (hs2.mul_left 2)
      refine h.congr (fun k => ?_)
      ring
    refine Summable.of_nonneg_of_le hbndnn (fun k => ?_) hdom
    simp only [hbnddef]
    have hp : (0 : ℝ) < (4 : ℝ) ^ (k + 1) := by positivity
    have hx1 : (1 : ℝ) ≤ (4 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hlog : Real.log (2 + (4 : ℝ) ^ (k + 1)) ≤
        ((k : ℝ) + 2) * Real.log 4 := by
      have hle : (2 : ℝ) + (4 : ℝ) ^ (k + 1) ≤ (4 : ℝ) ^ (k + 2) := by
        have hnext : (4 : ℝ) ^ (k + 2) = 4 * (4 : ℝ) ^ (k + 1) := by ring
        rw [hnext]
        nlinarith [hx1]
      calc
        Real.log (2 + (4 : ℝ) ^ (k + 1)) ≤
            Real.log ((4 : ℝ) ^ (k + 2)) :=
          Real.log_le_log (by positivity) hle
        _ = ((k : ℝ) + 2) * Real.log 4 := by
          rw [Real.log_pow]
          push_cast
          ring
    have hlin : (1 : ℝ) + (4 : ℝ) ^ (k + 1) ≤ 5 * (4 : ℝ) ^ k := by
      have h4k : (4 : ℝ) ^ (k + 1) = 4 * (4 : ℝ) ^ k := by ring
      have h1k : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      rw [h4k]
      linarith
    have hkey : (1 / 8 : ℝ) ^ k * (4 : ℝ) ^ k = (1 / 2) ^ k := by
      rw [← mul_pow]
      norm_num
    have hlog0 : 0 ≤ Real.log (2 + (4 : ℝ) ^ (k + 1)) :=
      Real.log_nonneg (by nlinarith [hp])
    calc
      (1 / 8 : ℝ) ^ k *
          (C * (1 + (4 : ℝ) ^ (k + 1)) *
            Real.log (2 + (4 : ℝ) ^ (k + 1))) ≤
          (1 / 8 : ℝ) ^ k *
            (C * (5 * (4 : ℝ) ^ k) * (((k : ℝ) + 2) * Real.log 4)) := by
              gcongr
      _ = 5 * C * Real.log 4 * (((k : ℝ) + 2) * (1 / 2) ^ k) := by
        rw [← hkey]
        ring
  set B : ℝ := ∑' k, bnd k with hBdef
  have hLF : LocallyFiniteSupport D.toFun :=
    Function.locallyFinsupp.locallyFiniteSupport D
  have hcore_fin : {ρ : ↥D.support | ‖(ρ : ℂ) - 2‖ < 4}.Finite := by
    apply Set.Finite.of_finite_image _ (Subtype.val_injective.injOn)
    apply Set.Finite.subset
      (hLF.finite_inter_support_of_isCompact (isCompact_closedBall (2 : ℂ) 4))
    rintro z ⟨ρ, hρ, rfl⟩
    exact ⟨by rw [mem_closedBall, dist_eq_norm]; exact le_of_lt hρ, ρ.2⟩
  set coreFin := hcore_fin.toFinset with hcoreFin
  set P : ↥D.support → Prop := fun ρ => ‖(ρ : ℂ) - 2‖ < 4 with hP
  refine summable_of_sum_le
    (c := (∑ ρ ∈ coreFin, f ρ) + 4 * B) hfnn (fun u => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not u P f]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      rw [hcoreFin, Set.Finite.mem_toFinset]
      exact (Finset.mem_filter.mp hρ).2
    · intro ρ _ _
      exact hfnn ρ
  · set uf := u.filter (fun ρ => ¬ P ρ) with hufdef
    have hfar4 : ∀ ρ ∈ uf, (4 : ℝ) ≤ ‖(ρ : ℂ) - 2‖ := by
      intro ρ hρ
      have h := (Finset.mem_filter.mp hρ).2
      simp only [hP, not_lt] at h
      exact h
    set G : ↥D.support → ℝ := fun ρ =>
      4 * (D (ρ : ℂ) : ℝ) * (1 / 8) ^ xiShellFour (ρ : ℂ) with hGdef
    have hfG : ∀ ρ ∈ uf, f ρ ≤ G ρ := by
      intro ρ hρ
      have hb4 : (4 : ℝ) ≤ ‖(ρ : ℂ) - 2‖ := hfar4 ρ hρ
      have hd : (0 : ℝ) ≤ (D (ρ : ℂ) : ℝ) := by
        exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
      have hab : ‖(ρ : ℂ) - 2‖ / 2 ≤ ‖(ρ : ℂ)‖ := by
        have htri : ‖(ρ : ℂ) - 2‖ ≤ ‖(ρ : ℂ)‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2] at htri
        linarith
      have hbs : (4 : ℝ) ^ xiShellFour (ρ : ℂ) ≤ ‖(ρ : ℂ) - 2‖ :=
        four_pow_xiShellFour_le hb4
      have hkey := shell_term_bound_three_halves
        (a := ‖(ρ : ℂ)‖) (b := ‖(ρ : ℂ) - 2‖)
        (d := (D (ρ : ℂ) : ℝ)) (s := xiShellFour (ρ : ℂ))
        hd hb4 hab hbs
      simp only [hfdef, hGdef]
      exact hkey
    calc
      ∑ ρ ∈ uf, f ρ ≤ ∑ ρ ∈ uf, G ρ := Finset.sum_le_sum hfG
      _ = ∑ b ∈ uf.image (fun ρ : ↥D.support => xiShellFour (ρ : ℂ)),
          ∑ ρ ∈ uf.filter (fun ρ : ↥D.support => xiShellFour (ρ : ℂ) = b),
            G ρ :=
        (Finset.sum_fiberwise_of_maps_to
          (fun ρ hρ => Finset.mem_image_of_mem
            (fun ρ : ↥D.support => xiShellFour (ρ : ℂ)) hρ) G).symm
      _ ≤ ∑ b ∈ uf.image (fun ρ : ↥D.support => xiShellFour (ρ : ℂ)),
          4 * bnd b := by
        apply Finset.sum_le_sum
        intro b _
        set fib := uf.filter
          (fun ρ : ↥D.support => xiShellFour (ρ : ℂ) = b) with hfibdef
        set r : ℝ := (4 : ℝ) ^ (b + 1) with hrdef
        have hr1 : (1 : ℝ) ≤ r := by
          rw [hrdef]
          exact one_le_pow₀ (by norm_num)
        have hmem : ∀ ρ ∈ fib, (ρ : ℂ) ∈ closedBall (2 : ℂ) r := by
          intro ρ hρ
          have hb' : xiShellFour (ρ : ℂ) = b := (Finset.mem_filter.mp hρ).2
          rw [mem_closedBall, dist_eq_norm, hrdef, ← hb']
          exact le_of_lt (norm_lt_four_pow_xiShellFour_succ (ρ : ℂ))
        set Db := MeromorphicOn.divisor xi (closedBall (2 : ℂ) r) with hDb
        have hrestrEq : D.restrict (Set.subset_univ (closedBall (2 : ℂ) r)) = Db :=
          MeromorphicOn.divisor_restrict xi_analyticOnNhd_univ.meromorphicOn _
        have hrestr : ∀ z ∈ closedBall (2 : ℂ) r, D z = Db z := by
          intro z hz
          rw [← hrestrEq, Function.locallyFinsuppWithin.restrict_apply, if_pos hz]
        have hDbfin : (Function.support ⇑Db).Finite :=
          Db.finiteSupport (isCompact_closedBall _ _)
        have hZ : (∑ ρ ∈ fib, D (ρ : ℂ)) ≤ ∑ᶠ v, Db v := by
          calc
            (∑ ρ ∈ fib, D (ρ : ℂ)) = ∑ ρ ∈ fib, Db (ρ : ℂ) :=
              Finset.sum_congr rfl (fun ρ hρ => hrestr (ρ : ℂ) (hmem ρ hρ))
            _ = ∑ z ∈ fib.image Subtype.val, Db z :=
              (Finset.sum_image (fun a _ b _ h => Subtype.ext h)).symm
            _ ≤ ∑ z ∈ hDbfin.toFinset, Db z := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro z hz
                rw [Finset.mem_image] at hz
                obtain ⟨ρ, hρ, rfl⟩ := hz
                rw [Set.Finite.mem_toFinset]
                apply Function.mem_support.mpr
                rw [← hrestr (ρ : ℂ) (hmem ρ hρ)]
                exact Function.mem_support.mp ρ.2
              · intro z _ _
                exact xi_divisor_nonneg _ z
            _ = ∑ᶠ v, Db v :=
              (finsum_eq_finsetSum_of_support_subset Db
                (by rw [hDbfin.coe_toFinset])).symm
        have hmass : ((∑ ρ ∈ fib, D (ρ : ℂ) : ℤ) : ℝ) ≤
            C * (1 + r) * Real.log (2 + r) := by
          calc
            ((∑ ρ ∈ fib, D (ρ : ℂ) : ℤ) : ℝ) ≤
                ((∑ᶠ v, Db v : ℤ) : ℝ) := by exact_mod_cast hZ
            _ ≤ C * (1 + r) * Real.log (2 + r) := hN r hr1
        have hshell_eq : ∀ ρ ∈ fib,
            G ρ = (4 * (1 / 8) ^ b) * (D (ρ : ℂ) : ℝ) := by
          intro ρ hρ
          have hb' : xiShellFour (ρ : ℂ) = b := (Finset.mem_filter.mp hρ).2
          simp only [hGdef]
          rw [hb']
          ring
        have hpref : (0 : ℝ) ≤ 4 * (1 / 8 : ℝ) ^ b := by positivity
        calc
          ∑ ρ ∈ fib, G ρ =
              ∑ ρ ∈ fib, (4 * (1 / 8) ^ b) * (D (ρ : ℂ) : ℝ) :=
            Finset.sum_congr rfl hshell_eq
          _ = (4 * (1 / 8) ^ b) *
              ((∑ ρ ∈ fib, D (ρ : ℂ) : ℤ) : ℝ) := by
            rw [← Finset.mul_sum]
            push_cast
            ring
          _ ≤ (4 * (1 / 8) ^ b) *
              (C * (1 + r) * Real.log (2 + r)) :=
            mul_le_mul_of_nonneg_left hmass hpref
          _ = 4 * bnd b := by
            simp only [hbnddef, hrdef]
            ring
      _ = 4 * ∑ b ∈ uf.image
          (fun ρ : ↥D.support => xiShellFour (ρ : ℂ)), bnd b := by
        rw [Finset.mul_sum]
      _ ≤ 4 * B := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [hBdef]
        exact hbndsum.sum_le_tsum _ (fun i _ => hbndnn i)

/-- The reciprocal-three-halves summability survives centering at the
functional-equation fixed point. -/
theorem xi_zero_multiplicity_centered_inv_three_halves_summable :
    Summable (fun ρ : XiDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ) - 1 / 2‖ * Real.sqrt ‖(ρ : ℂ) - 1 / 2‖)) := by
  classical
  set D := MeromorphicOn.divisor xi Set.univ with hD
  set f : ↥D.support → ℝ := fun ρ =>
    ((D (ρ : ℂ) : ℝ)) / (‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖) with hf
  set g : ↥D.support → ℝ := fun ρ =>
    ((D (ρ : ℂ) : ℝ)) /
      (‖(ρ : ℂ) - 1 / 2‖ * Real.sqrt ‖(ρ : ℂ) - 1 / 2‖) with hg
  have hf_sum : Summable f := by
    simpa only [f, hD] using xi_zero_multiplicity_inv_three_halves_summable
  have hdom : Summable (fun ρ => 4 * f ρ) := hf_sum.mul_left 4
  have hLF : LocallyFiniteSupport D.toFun :=
    Function.locallyFinsupp.locallyFiniteSupport D
  have hsmall : {ρ : ↥D.support | ‖(ρ : ℂ)‖ < 1}.Finite := by
    apply Set.Finite.of_finite_image _ (Subtype.val_injective.injOn)
    apply Set.Finite.subset
      (hLF.finite_inter_support_of_isCompact (isCompact_closedBall (0 : ℂ) 1))
    rintro z ⟨ρ, hρ, rfl⟩
    exact ⟨by simpa [mem_closedBall] using le_of_lt hρ, ρ.2⟩
  have hg_sum : Summable g := hdom.of_norm_bounded_eventually (by
    filter_upwards [hsmall.eventually_cofinite_notMem] with ρ hρ
    simp only [not_lt] at hρ
    have hd : (0 : ℝ) ≤ (D (ρ : ℂ) : ℝ) := by
      exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
    have hbpos : (0 : ℝ) < ‖(ρ : ℂ)‖ := lt_of_lt_of_le zero_lt_one hρ
    have htri : ‖(ρ : ℂ)‖ ≤ ‖(ρ : ℂ) - 1 / 2‖ + 1 / 2 := by
      calc
        ‖(ρ : ℂ)‖ = ‖((ρ : ℂ) - 1 / 2) + 1 / 2‖ := by ring_nf
        _ ≤ ‖(ρ : ℂ) - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
        _ = ‖(ρ : ℂ) - 1 / 2‖ + 1 / 2 := by norm_num
    have hab : ‖(ρ : ℂ)‖ / 2 ≤ ‖(ρ : ℂ) - 1 / 2‖ := by linarith
    have hapos : (0 : ℝ) < ‖(ρ : ℂ) - 1 / 2‖ :=
      lt_of_lt_of_le (half_pos hbpos) hab
    have hsqrt_half : Real.sqrt ‖(ρ : ℂ)‖ / 2 ≤
        Real.sqrt (‖(ρ : ℂ)‖ / 2) := by
      have hsq1 := Real.sq_sqrt (norm_nonneg (ρ : ℂ))
      have hsq2 := Real.sq_sqrt (by positivity : 0 ≤ ‖(ρ : ℂ)‖ / 2)
      have hs1 := Real.sqrt_nonneg ‖(ρ : ℂ)‖
      have hs2 := Real.sqrt_nonneg (‖(ρ : ℂ)‖ / 2)
      nlinarith
    have hsqrth : Real.sqrt (‖(ρ : ℂ)‖ / 2) ≤
        Real.sqrt ‖(ρ : ℂ) - 1 / 2‖ := Real.sqrt_le_sqrt hab
    have hdenom : ‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖ / 4 ≤
        ‖(ρ : ℂ) - 1 / 2‖ * Real.sqrt ‖(ρ : ℂ) - 1 / 2‖ := by
      calc
        ‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖ / 4 =
            (‖(ρ : ℂ)‖ / 2) * (Real.sqrt ‖(ρ : ℂ)‖ / 2) := by ring
        _ ≤ (‖(ρ : ℂ)‖ / 2) * Real.sqrt (‖(ρ : ℂ)‖ / 2) := by gcongr
        _ ≤ ‖(ρ : ℂ) - 1 / 2‖ *
            Real.sqrt ‖(ρ : ℂ) - 1 / 2‖ := by gcongr
    have hcomp :
        (D (ρ : ℂ) : ℝ) /
            (‖(ρ : ℂ) - 1 / 2‖ * Real.sqrt ‖(ρ : ℂ) - 1 / 2‖) ≤
          4 * ((D (ρ : ℂ) : ℝ) /
            (‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖)) := by
      calc
        (D (ρ : ℂ) : ℝ) /
            (‖(ρ : ℂ) - 1 / 2‖ * Real.sqrt ‖(ρ : ℂ) - 1 / 2‖) ≤
            (D (ρ : ℂ) : ℝ) /
              (‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖ / 4) :=
          div_le_div_of_nonneg_left hd (by positivity) hdenom
        _ = 4 * ((D (ρ : ℂ) : ℝ) /
            (‖(ρ : ℂ)‖ * Real.sqrt ‖(ρ : ℂ)‖)) := by
          field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ g ρ)]
    simpa only [hg, hf] using hcomp)
  simpa only [g, hD] using hg_sum

/-- Reciprocal exponent `3/2` over the exact multiplicity-copy index of the
centered Xi divisor. -/
theorem xiSpectralPoint_inv_three_halves_summable :
    Summable (fun q : XiZeroCopy =>
      1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  constructor
  · intro ρ
    exact (hasSum_fintype _).summable
  · refine xi_zero_multiplicity_centered_inv_three_halves_summable.congr
      (fun ρ => ?_)
    symm
    rw [tsum_fintype]
    simp only [norm_xiSpectralPoint]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support ρ)
    have hcast :
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℝ) =
          ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast, div_eq_mul_inv]
    ring

end

end RHTower
