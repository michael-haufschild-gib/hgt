import GaloisForLFunctions.RHTower.MobiusDivisorDyadicShellDebtGrowth

/-!
# Dyadic shell debt persists under any fixed old prime core

At scale near `4N`, products of two shell primes cannot reach the head.
Their one-prime contributions remain uniformly negative even after an
arbitrary fixed core has been processed, because every old prime is inactive
on the child arguments `x/p < 2`. The old core contributes only its own
square-root amplitude. Quantitative PNT makes the shell prime count dominate
that fixed amplitude, forcing the physical inverse-cube mean to diverge.

This is a necessary changing-core compensation law, not an all-cutoff
payment schedule or an RH proof.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private theorem head_eq_base_below_added (Q P : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hP : ∀ p ∈ P, p.Prime)
    (hdis : Disjoint Q P) {x : ℝ} (hx : ∀ p ∈ P, x ≤ p) :
    mobiusDivisorContinuousHead (Q ∪ P) x = mobiusDivisorContinuousHead Q x := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (mem_insert_self p P)
    have hPP : ∀ r ∈ P, r.Prime := fun r hr => hP r (mem_insert_of_mem hr)
    have hQP : ∀ r ∈ Q ∪ P, r.Prime := by
      intro r hr
      rcases mem_union.mp hr with h | h
      · exact hQ r h
      · exact hPP r h
    have hpQP : p ∉ Q ∪ P := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact disjoint_left.mp hdis h (mem_insert_self p P)
      · exact hpP h
    rw [Finset.union_insert, mobiusDivisorContinuousHead_insert (Q ∪ P) hQP hp hpQP]
    rw [mobiusDivisorContinuousHead_eq_zero (Q ∪ P)
      ((div_le_one (by exact_mod_cast hp.pos)).mpr (hx p (mem_insert_self p P)))]
    simpa using ih hPP (hdis.mono_right (subset_insert p P))
      (fun r hr => hx r (mem_insert_of_mem hr))

theorem head_shell_over_base (Q P : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hP : ∀ p ∈ P, p.Prime)
    (hdis : Disjoint Q P) {x : ℝ}
    (hpair : ∀ p ∈ P, ∀ r ∈ P, x ≤ (p:ℝ)*r) :
    mobiusDivisorContinuousHead (Q ∪ P) x =
      mobiusDivisorContinuousHead Q x -
        ∑ p ∈ P, Real.sqrt p * mobiusDivisorContinuousHead Q (x/p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (mem_insert_self p P)
    have hPP : ∀ r ∈ P, r.Prime := fun r hr => hP r (mem_insert_of_mem hr)
    have hQP : ∀ r ∈ Q ∪ P, r.Prime := by
      intro r hr
      rcases mem_union.mp hr with h | h
      · exact hQ r h
      · exact hPP r h
    have hpQP : p ∉ Q ∪ P := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact disjoint_left.mp hdis h (mem_insert_self p P)
      · exact hpP h
    have hbelow : mobiusDivisorContinuousHead (Q ∪ P) (x/p) =
        mobiusDivisorContinuousHead Q (x/p) := by
      apply head_eq_base_below_added Q P hQ hPP
        (hdis.mono_right (subset_insert p P))
      intro r hr
      exact (div_le_iff₀ (by exact_mod_cast hp.pos)).mpr
        (by simpa only [mul_comm] using
          (hpair p (mem_insert_self p P) r (mem_insert_of_mem hr)))
    rw [Finset.union_insert, mobiusDivisorContinuousHead_insert (Q ∪ P) hQP hp hpQP]
    rw [ih hPP (hdis.mono_right (subset_insert p P))
      (fun q hq r hr => hpair q (mem_insert_of_mem hq) r (mem_insert_of_mem hr)),
      hbelow, sum_insert hpP]
    ring

private theorem anchor_shell_defect_floor : (1/10:ℝ) ≤ primeFreeDivisorDefect 1 := by
  have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
  norm_num [harmonic, Finset.sum_range_succ, Real.log_four_eq] at h
  norm_num [primeFreeDivisorDefect]
  linarith [Real.log_two_lt_d9]

theorem anchor_shell_term_floor {N p : ℕ} (hN : 1 ≤ N)
    (hp : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N))
    {x : ℝ} (hxl : (7/2:ℝ)*N ≤ x) (hxu : x ≤ (15/4:ℝ)*N) :
    Real.sqrt N/200 ≤ Real.sqrt p * divisorContinuousUnitHead (x/p) := by
  obtain ⟨hprime,hpl,hpu⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hplR : (2:ℝ)*N < p := by exact_mod_cast hpl
  have hpuR : (p:ℝ) ≤ 3*N := by exact_mod_cast hpu
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x/p := (le_div_iff₀ hp0).mpr (by linarith)
  have hx2 : x/p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hfirst : divisorContinuousUnitHead (x/p) =
      (Real.sqrt (x/p)-1)*primeFreeDivisorDefect 1 := by
    rw [divisorContinuousUnitHead_between (k := 1) le_rfl (by simpa using hx1)
      (by simpa using hx2)]
    simp [divisorUnsignedDilationChannel]
  have hroot : Real.sqrt p*(Real.sqrt (x/p)-1) = Real.sqrt x-Real.sqrt p := by
    rw [Real.sqrt_div hx0]
    have hs : Real.sqrt (p:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
    field_simp
  have hrootp : Real.sqrt p ≤ (7/4:ℝ)*Real.sqrt N := by
    have hpSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg (p:ℝ), Real.sqrt_nonneg (N:ℝ)]
  have hrootx : (9/5:ℝ)*Real.sqrt N ≤ Real.sqrt x := by
    have hxSq := Real.sq_sqrt hx0
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (N:ℝ)]
  have hgap : Real.sqrt N/20 ≤ Real.sqrt x-Real.sqrt p := by linarith
  have h1 := mul_le_mul_of_nonneg_right anchor_shell_defect_floor
    (show 0 ≤ Real.sqrt N/20 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ primeFreeDivisorDefect 1 by linarith [anchor_shell_defect_floor])
  rw [hfirst]
  calc
    Real.sqrt N/200 ≤ primeFreeDivisorDefect 1 * (Real.sqrt x-Real.sqrt p) := by
      nlinarith only [h1,h2]
    _ = Real.sqrt p * ((Real.sqrt (x/p)-1)*primeFreeDivisorDefect 1) := by
      rw [← hroot]
      ring

/-- A dense fresh shell overwhelms any old core whose own physical head has
    bounded square-root amplitude. This retains the literal mixed source. -/
theorem shell_head_over_anchor_bound (Q : Finset ℕ) (hQ : ∀q∈Q,q.Prime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      Disjoint Q (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) →
      ∀ x : ℝ, (7/2:ℝ)*N ≤ x → x ≤ (15/4:ℝ)*N →
      mobiusDivisorContinuousHead
        (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) x ≤
      (2*C - ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)/200) *
        Real.sqrt N := by
  obtain ⟨C,hC,hbound⟩ := exists_bound_mobiusDivisorContinuousHead Q
  refine ⟨C,hC,?_⟩
  intro N hN hdis x hxl hxu
  let P := GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)
  have hprime : ∀ p∈P,p.Prime := fun p hp =>
    (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).1
  have hpair : ∀ p∈P,∀ r∈P,x ≤ (p:ℝ)*r := by
    intro p hp r hr
    have hpl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.1
    have hrl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hr).2.1
    have hp2 : (2:ℝ)*N ≤ p := by exact_mod_cast hpl.le
    have hr2 : (2:ℝ)*N ≤ r := by exact_mod_cast hrl.le
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hm := mul_le_mul hp2 hr2 (by positivity) (by positivity)
    nlinarith only [hm,hxu,hN1]
  have hunit : ∀ p∈P,mobiusDivisorContinuousHead Q (x/p) =
      divisorContinuousUnitHead (x/p) := by
    intro p hp
    have hpp := hprime p hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
    have hpl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.1
    have hplR : (2:ℝ)*N < p := by exact_mod_cast hpl
    have hxdiv : x/p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
    have h := head_eq_base_below_added ∅ Q (by simp) hQ (by simp)
      (x := x/p) (fun q hq => hxdiv.trans (by exact_mod_cast (hQ q hq).two_le))
    simpa [mobiusDivisorContinuousHead] using h
  have hsum : (P.card:ℝ)*Real.sqrt N/200 ≤
      ∑ p∈P,Real.sqrt p*mobiusDivisorContinuousHead Q (x/p) := by
    calc
      _ = ∑ _p∈P,Real.sqrt N/200 := by
        simp only [sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := sum_le_sum (fun p hp => by
        rw [hunit p hp]
        exact anchor_shell_term_floor hN hp hxl hxu)
  have hx0 : 0 ≤ x := by
    have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    linarith
  have hroot : Real.sqrt x ≤ 2*Real.sqrt N := by
    have hxSq := Real.sq_sqrt hx0
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg x,Real.sqrt_nonneg (N:ℝ)]
  have hCroot := mul_le_mul_of_nonneg_left hroot hC
  have hbase := (le_abs_self (mobiusDivisorContinuousHead Q x)).trans (hbound x)
  have heq := head_shell_over_base Q P hQ hprime hdis hpair
  rw [heq]
  dsimp only [P] at hsum ⊢
  nlinarith only [hsum,hbase,hCroot]

theorem anchor_shell_mean_lower_of_head
    (Q : Finset ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hhead : ∀ x : ℝ, (7/2:ℝ)*N ≤ x → x ≤ (15/4:ℝ)*N →
      mobiusDivisorContinuousHead
        (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) x ≤
      -((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)*
        Real.sqrt N/400) :
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)^2 /
      (40960000*(N:ℝ)) ≤
    mobiusDivisorDilationMean
      (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
  let P := GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)
  let T := Q ∪ P
  let a : ℝ := (7/2:ℝ)*N
  let b : ℝ := (15/4:ℝ)*N
  let K : ℝ := ((P.card:ℝ)*Real.sqrt N/400)^2 / (4*(N:ℝ))^3
  let f : ℝ → ℝ := fun x => (mobiusDivisorContinuousHead T x)^2/x^3
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have ha1 : 1 < a := by dsimp [a]; linarith
  have hset : Ioc a b ⊆ Ioi (1:ℝ) := by
    intro x hx
    exact ha1.trans hx.1
  have hint : IntegrableOn f (Ioi (1:ℝ)) := by
    simpa only [f, one_mul, pow_two] using
      integrable_mobiusDivisorDilationMean_kernel T (by norm_num : (0:ℝ)<1)
  have hpt : ∀ x ∈ Ioc a b, K ≤ f x := by
    intro x hx
    have hxl : (7/2:ℝ)*N ≤ x := hx.1.le
    have hxu : x ≤ (15/4:ℝ)*N := hx.2
    have hh := hhead x hxl hxu
    have hx0 : 0 < x := lt_trans zero_lt_one (ha1.trans hx.1)
    have hx4 : x ≤ 4*(N:ℝ) := by linarith
    have hden : x^3 ≤ (4*(N:ℝ))^3 := pow_le_pow_left₀ hx0.le hx4 3
    have hsq : ((P.card:ℝ)*Real.sqrt N/400)^2 ≤
        (mobiusDivisorContinuousHead T x)^2 := by
      have hK : 0 ≤ (P.card:ℝ)*Real.sqrt N/400 := by positivity
      have hh' : (P.card:ℝ)*Real.sqrt N/400 ≤
          -mobiusDivisorContinuousHead T x := by
        dsimp only [T,P] at hh ⊢
        linarith only [hh]
      have hpow := pow_le_pow_left₀ hK hh' 2
      nlinarith only [hpow]
    have hmul : ((P.card:ℝ)*Real.sqrt N/400)^2*x^3 ≤
        (mobiusDivisorContinuousHead T x)^2*(4*(N:ℝ))^3 :=
      mul_le_mul hsq hden (by positivity) (by positivity)
    exact (div_le_div_iff₀ (by positivity : 0 < (4*(N:ℝ))^3)
      (pow_pos hx0 3)).mpr hmul
  have hmono : K*(b-a) ≤ ∫ x in Ioc a b, f x := by
    have hconst : IntegrableOn (fun _ : ℝ => K) (Ioc a b) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hm := setIntegral_mono_on hconst
      (hint.mono_set hset) measurableSet_Ioc hpt
    have hvol : (volume : Measure ℝ).real (Ioc a b) = b-a := by
      simp [MeasureTheory.measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal, sub_nonneg.mpr hab]
    simpa only [setIntegral_const, smul_eq_mul, hvol, mul_comm] using hm
  have hmass : (∫ x in Ioc a b, f x) ≤ ∫ x in Ioi (1:ℝ), f x := by
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact div_nonneg (sq_nonneg _) (pow_nonneg (le_trans zero_le_one hx.le) 3)
    · exact Filter.Eventually.of_forall (fun x hx => hset hx)
  have hlen : b-a=(N:ℝ)/4 := by dsimp [a,b]; ring
  rw [hlen] at hmono
  have hraw : K*((N:ℝ)/4) ≤ mobiusDivisorDilationMean T 1 :=
    hmono.trans (by simpa [mobiusDivisorDilationMean, f, one_mul,
      pow_two] using hmass)
  have hN0 : (N:ℝ) ≠ 0 := hNr.ne'
  have heq : K*((N:ℝ)/4) = (P.card:ℝ)^2/(40960000*(N:ℝ)) := by
    dsimp [K]
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
    field_simp [hN0]
    ring
  dsimp only [T,P] at hraw ⊢
  rwa [heq] at hraw

/-- Shell debt remains large after any finite old core once shell count exceeds
    that core's square-root amplitude by the explicit factor 800. -/
theorem exists_anchor_shell_debt_threshold (Q : Finset ℕ)
    (hQ : ∀q∈Q,q.Prime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      Disjoint Q (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) →
      800*C ≤ ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ) →
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)^2 /
        (40960000*(N:ℝ)) ≤
      mobiusDivisorDilationMean
        (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
  obtain ⟨C,hC,hhead⟩ := shell_head_over_anchor_bound Q hQ
  refine ⟨C,hC,?_⟩
  intro N hN hdis hcard
  apply anchor_shell_mean_lower_of_head Q N hN
  intro x hxl hxu
  have h := hhead N hN hdis x hxl hxu
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith only [h,hcard,hs,mul_nonneg
    (show (0:ℝ) ≤
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)-800*C by linarith) hs]

/-- Every fixed processed old core fails to pay the physical dyadic-shell
    debt: the inverse-cube mean still diverges as the shell moves outward. -/
theorem tendsto_shell_dilationMean_over_fixed_anchor_atTop
    (Q : Finset ℕ) (hQ : ∀q∈Q,q.Prime) :
    Tendsto (fun N : ℕ => mobiusDivisorDilationMean
      (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1)
      atTop atTop := by
  obtain ⟨C,hC,hdebt⟩ := exists_anchor_shell_debt_threshold Q hQ
  let k : ℕ → ℝ := fun N =>
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)
  have hcardTop : Tendsto (fun N : ℕ => k N/Real.sqrt N) atTop atTop :=
    tendsto_shell_card_div_sqrt
  have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)
  have hscaled : Tendsto (fun N : ℕ => (k N/Real.sqrt N)^2/40960000)
      atTop atTop :=
    (hpow.comp hcardTop).atTop_div_const (by norm_num : (0:ℝ)<40960000)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (k N/Real.sqrt N)^2/40960000 ≤
        mobiusDivisorDilationMean
          (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
    filter_upwards [hcardTop.eventually_ge_atTop (800*C),
      eventually_ge_atTop (max 1 (∑ q∈Q,q))] with N hk hN
    have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
    have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
    have hroot1 : 1 ≤ Real.sqrt N := by
      have hN1R : (1:ℝ) ≤ N := by exact_mod_cast hN1
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N),
        Real.sqrt_nonneg (N:ℝ)]
    have hdis : Disjoint Q
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) := by
      apply Finset.disjoint_left.mpr
      intro p hpQ hpP
      have hq : p ≤ ∑ q∈Q,q :=
        Finset.single_le_sum (fun q _ => Nat.zero_le q) hpQ
      have hpl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hpP).2.1
      omega
    have hk' : 800*C ≤ k N := by
      have hmul := (le_div_iff₀ hroot).mp hk
      nlinarith only [hmul,hroot1,hC,mul_nonneg
        (show (0:ℝ) ≤ 800*C by positivity) (sub_nonneg.mpr hroot1)]
    have hlower := hdebt N hN1 hdis hk'
    have hN0 : (N:ℝ) ≠ 0 := hNr.ne'
    have heq : (k N/Real.sqrt N)^2/40960000 =
        (k N)^2/(40960000*(N:ℝ)) := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
      field_simp [hN0]
    rw [heq]
    exact hlower
  exact tendsto_atTop_mono' _ hbound hscaled

end RHTower
