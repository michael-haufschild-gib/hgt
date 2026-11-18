import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOrdinaryPrimeErrorBelowAQuadraticProductCut
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SamplingTheMovingConductorEndpoints

/-!
# Subquadratic product shells under conductor rescaling

A common bound on the top product controls the entire rescaled integral.
Both lower and upper power cutoffs are retained in the ordinary prime
interval, including when the terminal conductor falls inside an octave.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem shell_mesh_exchange {N M H b : ℕ} (α β c : ℝ)
    (hgeom : ∀ n ∈ Ioc N M,
      let V := ⌊(n:ℝ)^α⌋₊
      let U := ⌊c*(n:ℝ)^β⌋₊
      V ≤ U ∧ U ≤ H ∧ U ≤ splineHorizon n ∧ productLower 1 (splineHorizon n) ≤ V ∧
        (U:ℝ)+1 < Real.exp (-8)*(n:ℝ)^2 ∧ splineHorizon n < b) :
    (∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading ⌊(n:ℝ)^α⌋₊ n -
        centeredProductReading ⌊c*(n:ℝ)^β⌋₊ n)) =
      ∑ q ∈ Ioc 0 H, (vonMangoldt q-1) *
        ∑ n ∈ Ioc N M with (n:ℝ)^α < q ∧ (q:ℝ) ≤ c*(n:ℝ)^β,
            (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2) := by
  let a := fun q : ℕ => vonMangoldt q-1
  let F (q n : ℕ) := (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)
  let keep (n q : ℕ) := (n:ℝ)^α < q ∧ (q:ℝ) ≤ c*(n:ℝ)^β
  have hrow (n : ℕ) (hn : n ∈ Ioc N M) :
      (n:ℝ)^2*(centeredProductReading ⌊(n:ℝ)^α⌋₊ n-centeredProductReading ⌊c*(n:ℝ)^β⌋₊ n) =
        ∑ q ∈ Ioc 0 H, if keep n q then a q*F q n else 0 := by
    let V := ⌊(n:ℝ)^α⌋₊
    let U := ⌊c*(n:ℝ)^β⌋₊
    obtain ⟨hVU,hUH,hUL,hY,hbefore,hb⟩ := hgeom n hn
    have hn0 := (Nat.zero_le N).trans_lt (mem_Ioc.mp hn).1
    have hs := detached_signed_product_shell hn0 hVU hUL hY hbefore a
    change centeredProductReading V n - centeredProductReading U n = _ at hs
    rw [hs,mul_sum,←sum_filter]
    have he : (Ioc 0 H).filter (keep n) = Ioc V U := by
      ext q
      simp only [V,U,keep,mem_filter,mem_Ioc,Nat.floor_lt
        (Real.rpow_nonneg (Nat.cast_nonneg n) α)]
      constructor
      · rintro ⟨⟨hq,_⟩,hl,hu⟩
        exact ⟨hl,Nat.le_floor hu⟩
      · rintro ⟨hl,hu⟩
        have hq : 0 < q := Nat.cast_pos.mp ((Real.rpow_nonneg (Nat.cast_nonneg n) α).trans_lt hl)
        exact ⟨⟨hq,hu.trans hUH⟩,hl,(Nat.le_floor_iff' hq.ne').mp hu⟩
    rw [he]
    apply sum_congr rfl
    intro q hq
    have hq0 := (Nat.zero_le V).trans_lt (mem_Ioc.mp hq).1
    have hqb := hb.trans_le (Nat.le_mul_of_pos_left b hq0)
    dsimp only [F]
    rw [←unitHorizonPair_real_profile hn0 hq0 hqb]
    ring
  rw [sum_congr rfl hrow,sum_comm]
  apply sum_congr rfl
  intro q _
  rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro n _
  by_cases h : keep n q <;> simp only [keep] at h <;> simp [keep,a,F,h]

private theorem shell_product_ceiling {n N : ℕ} (hn : n ≤ 2*N) {c : ℝ} (hc : c ≤ 2) :
    ⌊c*(n:ℝ)^(19/10:ℝ)⌋₊ ≤ ⌊8*(N:ℝ)^(19/10:ℝ)⌋₊ := by
  apply Nat.floor_mono
  have hi := Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.cast_le.mpr hn : (n:ℝ) ≤ (2*N:ℕ)) (by norm_num : (0:ℝ)≤19/10)
  push_cast at hi
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at hi
  have h2 : (2:ℝ)^(19/10:ℝ) ≤ 4 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (19/10:ℝ) ≤ 2)).trans_eq
    norm_num [Real.rpow_two]
  have hh := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg N) (19/10))
  linarith only [mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg n) (19/10)),hi,hh]

private theorem choose_mesh_cap (N M : ℕ) (hM : 0 < M) :
    ∃ b : ℕ, (∀ n ∈ Ioc N M, splineHorizon n < b) ∧ 4*Real.exp 8 < (b:ℝ)/(M:ℝ)^2 := by
  let L := ∑ n ∈ Ioc N M, splineHorizon n
  let R := 4*Real.exp 8*(M:ℝ)^2
  let b := max L ⌈R⌉₊ + 1
  refine ⟨b,fun n hn => ?_,?_⟩
  · have hL : splineHorizon n ≤ L := single_le_sum (fun i _ => Nat.zero_le (splineHorizon i)) hn
    exact (hL.trans (le_max_left _ _)).trans_lt (Nat.lt_succ_self _)
  · apply (lt_div_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr hM))).mpr
    exact (Nat.le_ceil R).trans_lt (Nat.cast_lt.mpr
      ((le_max_right L ⌈R⌉₊).trans_lt (Nat.lt_succ_self _)))

private theorem nineteen_tenths_top {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) (hM : M ≤ 2*N) :
    let H := ⌊8*(N:ℝ)^(19/10:ℝ)⌋₊
    let T := (N:ℝ)^(1/20:ℝ)/4
    1 ≤ H ∧ 0 < T ∧ T ≤ M ∧ T*Real.sqrt H ≤ N ∧
      (((M+1:ℕ):ℝ)*H+(H:ℝ)^(1+(8/9:ℝ))/T^12) ≤
        (24+8^(17/9:ℝ)*4^12)*(N:ℝ)^3 := by
  let X := (N:ℝ)^(19/10:ℝ)
  let U := (N:ℝ)^(1/20:ℝ)
  let V := (N:ℝ)^(19/20:ℝ)
  let H := ⌊8*X⌋₊
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 := zero_lt_one.trans_le hn
  have hU : 0 < U := Real.rpow_pos_of_pos hn0 _
  have hV : 0 < V := Real.rpow_pos_of_pos hn0 _
  have hX : 1 ≤ X := Real.one_le_rpow hn (by norm_num)
  have hX0 := zero_lt_one.trans_le hX
  have hH : (H:ℝ) ≤ 8*X := Nat.floor_le (by positivity)
  have hX2 : X ≤ (N:ℝ)^2 := (Real.rpow_le_rpow_of_exponent_le hn
    (by norm_num : (19/10:ℝ) ≤ 2)).trans_eq (Real.rpow_two _)
  have hU1 : U ≤ N := (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1/20:ℝ) ≤ 1)).trans_eq
    (Real.rpow_one _)
  have hUV : U*V = N := by dsimp only [U,V]; rw [←Real.rpow_add hn0,show (1/20:ℝ)+19/20=1 by norm_num,Real.rpow_one]
  have hVV : V^2=X := by
    dsimp only [V,X]
    rw [←Real.rpow_two,←Real.rpow_mul hn0.le,show (19/20:ℝ)*2=19/10 by norm_num]
  have hr : Real.sqrt H ≤ 4*V := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,hVV]
    linarith only [hH,hX0.le]
  have hTN : U/4*Real.sqrt H ≤ N := by
    have h := mul_le_mul_of_nonneg_left hr (div_nonneg hU.le (by norm_num : (0:ℝ)≤4))
    exact h.trans_eq (by rw [←hUV]; ring)
  refine ⟨Nat.le_floor (by linarith only [hX] : (1:ℝ) ≤ 8*X),div_pos hU (by norm_num),
    (div_le_self hU.le (by norm_num : (1:ℝ)≤4)).trans (hU1.trans (Nat.cast_le.mpr hNM)),hTN,?_⟩
  have hMp : ((M+1:ℕ):ℝ) ≤ 3*(N:ℝ) := by
    have hM' : (M:ℝ) ≤ (2*N:ℕ) := Nat.cast_le.mpr hM
    push_cast at hM' ⊢
    linarith only [hn,hM']
  have hQ := mul_le_mul hMp (hH.trans (mul_le_mul_of_nonneg_left hX2 (by norm_num)))
    (Nat.cast_nonneg H) (by positivity)
  have hUp : (N:ℝ)^3*U^12=(N:ℝ)^(18/5:ℝ) := by
    dsimp only [U]
    rw [←Real.rpow_natCast _ 12,←Real.rpow_mul hn0.le,←Real.rpow_natCast _ 3,←Real.rpow_add hn0]
    norm_num
  have hpow : (H:ℝ)^(17/9:ℝ) ≤ (8:ℝ)^(17/9:ℝ)*((N:ℝ)^3*U^12) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hH (by norm_num)).trans
    rw [Real.mul_rpow (by norm_num) hX0.le,hUp]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
    dsimp only [X]
    rw [←Real.rpow_mul hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hsign : (H:ℝ)^(1+(8/9:ℝ))/(U/4)^12 ≤ (8:ℝ)^(17/9:ℝ)*4^12*(N:ℝ)^3 := by
    apply (div_le_iff₀ (pow_pos (div_pos hU (by norm_num : (0:ℝ)<4)) 12)).mpr
    rw [show (1+(8/9:ℝ))=17/9 by norm_num]
    exact hpow.trans_eq (by ring)
  exact (add_le_add hQ hsign).trans_eq (by ring)

private theorem octave_conductor_log {N M : ℕ} (hN : 0 < N) (hM : M ≤ 2*N) :
    (M:ℝ)^3*conductorLog M ≤ 16*(N:ℝ)^3*conductorLog N := by
  by_cases hm0 : M=0
  · subst M
    simp only [Nat.cast_zero,zero_pow (by decide : 3≠0),zero_mul]
    exact mul_nonneg (by positivity) (zero_le_one.trans (conductorLog_one_le N))
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<2)
    (show (2:ℝ) ≤ 2*N by linarith only [hN'])
  have he : conductorLog (2*N) = Real.log 2+conductorLog N := by
    simp only [conductorLog,Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity : 2*(N:ℝ)≠0)]
    ring
  have hlog := conductorLog_mono (Nat.pos_of_ne_zero hm0) hM
  rw [he] at hlog
  have hL : conductorLog M ≤ 2*conductorLog N := by
    dsimp only [conductorLog] at hlog ⊢
    linarith only [hlog,hl]
  have hq := pow_le_pow_left₀ (Nat.cast_nonneg M) (Nat.cast_le.mpr hM : (M:ℝ) ≤ (2*N:ℕ)) 3
  push_cast at hq
  exact (mul_le_mul hq hL (zero_le_one.trans (conductorLog_one_le M)) (by positivity)).trans_eq (by ring)

private theorem include_initial_octaves (S : ℕ → ℝ) {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ {N M : ℕ}, k ≤ N → 0 < N → N ≤ M → M ≤ 2*N →
      |∑ n ∈ Ioc N M, S n| ≤ C*(N:ℝ)^3*conductorLog N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N M : ℕ}, N ≤ M → M ≤ 2*N →
      |∑ n ∈ Ioc N M, S n| ≤ K*(N:ℝ)^3*conductorLog N := by
  let A := ∑ n ∈ Icc 1 (2*k), |S n|
  have hA : 0 ≤ A := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C+A,add_nonneg hC hA,fun {N M} hNM hMN => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hm : M=0 := by omega
    simp [hm]
  have hN' : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hnorm := mul_le_mul (one_le_pow₀ (n := 3) hN') (conductorLog_one_le N) zero_le_one (by positivity)
  rw [one_mul] at hnorm
  by_cases hk : k ≤ N
  · exact (h hk hN hNM hMN).trans (by
      rw [mul_assoc,mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA) (zero_le_one.trans hnorm))
  · have hsub : Ioc N M ⊆ Icc 1 (2*k) := by
      intro n hn
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
      exact mem_Icc.mpr ⟨hN.trans hl.le,hu.trans (hMN.trans (Nat.mul_le_mul_left _ (Nat.le_of_not_ge hk)))⟩
    have hb := (abs_sum_le_sum_abs S (Ioc N M)).trans
      (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => abs_nonneg (S n)))
    rw [mul_assoc]
    exact hb.trans ((le_add_of_nonneg_left hC).trans (le_mul_of_one_le_right (add_nonneg hC hA) hnorm))

/-- Through every partial conductor octave, all products between two
floor power cuts up to the nineteen-tenths scale have cubic-logarithmic cost. -/
theorem capped_shell_to_nineteen_tenths {α c : ℝ} (hα : 1 < α) (hαβ : α ≤ 19/10)
    (hc : 1 ≤ c) (hc' : c ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N M : ℕ}, N ≤ M → M ≤ 2*N →
      |∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^α⌋₊ n n -
        cappedUpperProductReading ⌊c*(n:ℝ)^(19/10:ℝ)⌋₊ n n)| ≤ K*(N:ℝ)^3*conductorLog N := by
  let β : ℝ := 19/10
  let V (n : ℕ) := ⌊(n:ℝ)^α⌋₊
  let U (n : ℕ) := ⌊c*(n:ℝ)^β⌋₊
  let K0 : ℝ := 24+8^(17/9:ℝ)*4^12
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  obtain ⟨A,hA,ha⟩ := discrete_rescaled_shell_bound
  obtain ⟨B,hB,hb⟩ := shell_centering_transfer
  obtain ⟨k,hk⟩ := eventually_atTop.mp (subquadratic_cut_geometry hα hαβ (by norm_num) hc hc')
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(1/10:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp tendsto_natCast_atTop_atTop
  obtain ⟨j,hj⟩ := eventually_atTop.mp (ht.eventually_gt_atTop (112*Real.exp 8))
  apply include_initial_octaves (k := max k j) (C := A*K0+16*B) _ (by positivity)
  intro N M hkN hN hNM hMN
  let H := ⌊8*(N:ℝ)^β⌋₊
  let T := (N:ℝ)^(1/20:ℝ)/4
  have hn0 : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have htop := nineteen_tenths_top hN hNM hMN
  obtain ⟨hH,hT,hTM,hTN,hprice⟩ := htop
  obtain ⟨b,hbl,hbu⟩ := choose_mesh_cap N M (hN.trans_le hNM)
  have hsmall : 7/T^2 < Real.exp (-8) := by
    dsimp only [T]
    rw [div_pow,←Real.rpow_two ((N:ℝ)^(1/20:ℝ)),←Real.rpow_mul hn0.le,
      show (1/20:ℝ)*2=1/10 by norm_num,Real.exp_neg]
    have hg := hj N ((le_max_right k j).trans hkN)
    have hp := Real.rpow_pos_of_pos hn0 (1/10:ℝ)
    apply (div_lt_iff₀ (div_pos hp (by norm_num))).mpr
    rw [inv_mul_eq_div]
    apply (lt_div_iff₀ (Real.exp_pos 8)).mpr
    linarith only [hg]
  have hex := shell_mesh_exchange (N := N) (M := M) (H := H) (b := b) α β c (fun n hn => by
    obtain ⟨hV,hL,hY,hbirth⟩ := hk n (((le_max_left k j).trans hkN).trans (mem_Ioc.mp hn).1.le)
    exact ⟨hV,shell_product_ceiling ((mem_Ioc.mp hn).2.trans hMN) hc',hL,hY,hbirth,hbl n hn⟩)
  have hint := ha hN hNM hH b (zero_lt_one.trans hα) (hαβ.trans (by norm_num))
    (by norm_num [β] : 0<β) (by norm_num [β] : β≤2) (zero_lt_one.trans_le hc) hT hTM hTN le_rfl hsmall hbu
  have hcenter : |∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (V n) n -
      centeredProductReading (U n) n)| ≤ A*K0*(N:ℝ)^3 := by
    rw [hex]
    exact hint.trans ((mul_le_mul_of_nonneg_left hprice hA).trans_eq (by ring))
  let S := ∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading (V n) n n -
          cappedUpperProductReading (U n) n n)
  let D := ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (V n) n -
          centeredProductReading (U n) n)
  change |S| ≤ _
  have htri : |S| ≤ |S-D|+|D| := by simpa only [sub_add_cancel] using abs_add_le (S-D) D
  apply htri.trans ((add_le_add (hb V U N M) hcenter).trans _)
  have hoct := mul_le_mul_of_nonneg_left (octave_conductor_log hN hMN) hB
  have hd := le_mul_of_one_le_right (mul_nonneg (mul_nonneg hA hK0) (pow_nonneg hn0.le 3)) (conductorLog_one_le N)
  linarith only [hoct,hd]

private theorem one_product_row_error :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ k Y U V : ℕ, U ≤ V → V ≤ U+1 →
      |centeredProductTail k (max Y U)-centeredProductTail k (max Y V)| ≤ F*(1+Real.log k) := by
  obtain ⟨F,hF,hw⟩ := centeredPrimeWeight_uniform
  refine ⟨F,hF,fun k Y U V hUV hVU => ?_⟩
  let T := Ioc (max Y U) k
  let S := Ioc (max Y V) k
  let f := fun q : ℕ => (vonMangoldt q-1)*centeredPrimeWeight 1 (k/q)
  have hs : S ⊆ T := Ioc_subset_Ioc_left (max_le_max_left Y hUV)
  have hsingle : T ∖ S ⊆ {V} := by
    intro q hq
    obtain ⟨hT,hn⟩ := mem_sdiff.mp hq
    obtain ⟨hg,hk⟩ := mem_Ioc.mp hT
    have hl := max_lt_iff.mp hg
    have hqV : q ≤ V := le_of_not_gt fun h => hn (mem_Ioc.mpr ⟨max_lt hl.1 h,hk⟩)
    exact mem_singleton.mpr (by omega)
  have hsum := sum_sdiff (f := f) hs
  change |(∑ q ∈ T, f q) - ∑ q ∈ S, f q| ≤ _
  rw [show (∑ q ∈ T, f q) - ∑ q ∈ S, f q = ∑ q ∈ T ∖ S, f q by linarith only [hsum]]
  have hlog := Real.log_natCast_nonneg k
  have hcost : 0 ≤ F*(1+Real.log k) := by positivity
  calc _ ≤ ∑ _q ∈ T ∖ S, F*(1+Real.log k) := by
            apply (abs_sum_le_sum_abs _ _).trans
            apply sum_le_sum
            intro q hq
            obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_sdiff.mp hq).1
            have hq0 := (Nat.zero_le (max Y U)).trans_lt hl
            have hqlog := Real.log_le_log (Nat.cast_pos.mpr hq0) (Nat.cast_le.mpr hu)
            have hqabs : |vonMangoldt q-1| ≤ 1+Real.log k := by
              apply (abs_sub _ _).trans
              rw [abs_of_nonneg vonMangoldt_nonneg,abs_one,add_comm]
              exact add_le_add (le_refl (1:ℝ)) (vonMangoldt_le_log.trans hqlog)
            change |(vonMangoldt q-1)*centeredPrimeWeight 1 (k/q)| ≤ _
            rw [abs_mul,mul_comm F]
            exact mul_le_mul hqabs (by simpa only [Nat.cast_one,mul_one] using hw (R := 1) le_rfl (k/q))
              (abs_nonneg _) (by positivity)
       _ ≤ ∑ _q ∈ ({V}:Finset ℕ), F*(1+Real.log k) := sum_le_sum_of_subset_of_nonneg hsingle fun _ _ _ => hcost
       _ = _ := by rw [sum_singleton]

private theorem adjacent_cut_reading_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ U V : ℕ, U ≤ V → V ≤ U+1 →
      |centeredProductReading U n - centeredProductReading V n| ≤ C*conductorLog n/n := by
  obtain ⟨F,hF,hr⟩ := one_product_row_error
  obtain ⟨A,_,ha⟩ := successorSquare_window_bound
  obtain ⟨D,_,hD,_,hd⟩ := sampledSpline_differences
  obtain ⟨J,hJ,hj⟩ := splineHorizon_conductorLog
  refine ⟨A^2*F*J*D,by positivity,fun {n} hn U V hUV hVU => ?_⟩
  let L := splineHorizon n
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hcn := zero_le_one.trans (conductorLog_one_le n)
  unfold centeredProductReading splineCountReading
  rw [←sum_sub_distrib]
  simp_rw [←sub_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _k ∈ Icc 1 L, (F*(J*conductorLog n))*(D/(n:ℝ)^3) := by
              apply sum_le_sum
              intro k hk
              obtain ⟨hk1,hkL⟩ := mem_Icc.mp hk
              have hl := Real.log_le_log (Nat.cast_pos.mpr hk1) (Nat.cast_le.mpr hkL)
              rw [abs_mul]
              exact mul_le_mul ((hr k _ U V hUV hVU).trans (mul_le_mul_of_nonneg_left
                ((add_le_add (le_refl (1:ℝ)) hl).trans (hj hn)) hF)) ((hd hn k).1) (abs_nonneg _) (by positivity)
       _ ≤ (A*n)^2*((F*(J*conductorLog n))*(D/(n:ℝ)^3)) := by
              rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
              exact mul_le_mul_of_nonneg_right (ha hn) (by positivity)
       _ = _ := by field_simp <;> ring

private theorem double_floor_cut (x : ℝ) (hx : 0 ≤ x) :
    2*⌊x⌋₊ ≤ ⌊2*x⌋₊ ∧ ⌊2*x⌋₊ ≤ 2*⌊x⌋₊+1 := by
  constructor
  · apply Nat.le_floor
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hx) (by norm_num)
  · apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (mul_nonneg (by norm_num) hx)).mpr
    push_cast
    linarith only [Nat.lt_floor_add_one x]

/-- The actual nineteen-tenths shell with the integer upper cutoff twice the
floor, the original cofactor cap and every partial terminal endpoint. -/
theorem nineteen_tenths_shell_partial_octave :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N M : ℕ}, N ≤ M → M ≤ 2*N →
      let V := fun n : ℕ => ⌊(n:ℝ)^(19/10:ℝ)⌋₊
      |∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading (V n) n n -
        cappedUpperProductReading (2*V n) n n)| ≤ C*(N:ℝ)^3*conductorLog N := by
  let X := fun n : ℕ => (n:ℝ)^(19/10:ℝ)
  let V := fun n : ℕ => ⌊X n⌋₊
  let D := fun n => 2*V n
  let U := fun n => ⌊2*X n⌋₊
  obtain ⟨A,hA,ha⟩ := capped_shell_to_nineteen_tenths (α := 19/10) (c := 2) (by norm_num) le_rfl (by norm_num) le_rfl
  obtain ⟨B,hB,hb⟩ := shell_centering_transfer
  obtain ⟨C,hC,hc⟩ := adjacent_cut_reading_error
  refine ⟨A+16*(B+C),by positivity,fun {N M} hNM hMN => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hm : M=0 := by omega
    simp [hm]
  let S (i j : ℕ → ℕ) := ∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading (i n) n n -
    cappedUpperProductReading (j n) n n)
  let E := ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (D n) n - centeredProductReading (U n) n)
  have hE : |E| ≤ C*(M:ℝ)^3*conductorLog M := by
    have hL := zero_le_one.trans (conductorLog_one_le M)
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _n ∈ Ioc N M, (M:ℝ)^2*(C*conductorLog M) := by
              apply sum_le_sum
              intro n hn
              obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
              have hp := hN.trans_le hl.le
              have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hp
              obtain ⟨h₁,h₂⟩ := double_floor_cut (X n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              have hh := (hc hp (D n) (U n) h₁ h₂).trans (div_le_self
                (mul_nonneg hC (zero_le_one.trans (conductorLog_one_le n))) hn1)
              rw [abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]
              exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg n) (Nat.cast_le.mpr hu) 2)
                (hh.trans (mul_le_mul_of_nonneg_left (conductorLog_mono hp hu) hC)) (abs_nonneg _) (sq_nonneg _)
         _ ≤ (M:ℝ)*((M:ℝ)^2*(C*conductorLog M)) := by
              rw [sum_const,nsmul_eq_mul,Nat.card_Ioc]
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M N)) (by positivity)
         _ = _ := by ring
  have he : S V D = S V U - (S D U-E) - E := by
    have hs : S V D = S V U - S D U := by
      dsimp only [S]
      rw [←sum_sub_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [hs]; ring
  change |S V D| ≤ _
  rw [he]
  apply (abs_sub _ _).trans ((add_le_add ((abs_sub _ _).trans (add_le_add (ha hNM hMN) (hb D U N M))) hE).trans _)
  have hoct := octave_conductor_log hN hMN
  linarith only [mul_le_mul_of_nonneg_left hoct hB,mul_le_mul_of_nonneg_left hoct hC]

/-- The change of the actual signed prefix from the seventeen-ninths to the
nineteen-tenths product cut costs at most a cubic times one logarithm through
every terminal conductor. -/
theorem seventeenNinths_to_nineteenTenths_prefix :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      |∑ n ∈ Ioc 0 M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        cappedUpperProductReading ⌊(n:ℝ)^(19/10:ℝ)⌋₊ n n)| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨B,hB,hoct⟩ := capped_shell_to_nineteen_tenths (α := 17/9) (c := 1)
    (by norm_num) (by norm_num) le_rfl (by norm_num)
  simp only [one_mul] at hoct
  let f (n : ℕ) := (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
    cappedUpperProductReading ⌊(n:ℝ)^(19/10:ℝ)⌋₊ n n)
  let C := B+|f 1|
  have hC : 0 ≤ C := add_nonneg hB (abs_nonneg _)
  have hBC : B ≤ C := le_add_of_nonneg_right (abs_nonneg _)
  refine ⟨C,hC,fun M => ?_⟩
  change |∑ n ∈ Ioc 0 M, f n| ≤ _
  induction M using Nat.strong_induction_on with
  | h M ih =>
    rcases M with _ | _ | m
    · simp
    · have hs : Ioc 0 1 = ({1} : Finset ℕ) := by ext n; simp only [mem_Ioc,mem_singleton]; omega
      rw [hs,sum_singleton,Nat.cast_one,one_pow,mul_one]
      exact (le_add_of_nonneg_left hB).trans (le_mul_of_one_le_right hC (conductorLog_one_le 1))
    · let M := m+2
      let J := (M+1)/2
      have hJ : 0 < J := by dsimp only [J,M]; omega
      have hJM : J < M := by dsimp only [J,M]; omega
      have hMJ : M ≤ 2*J := by dsimp only [J,M]; omega
      have hrat : (J:ℝ) ≤ (2/3:ℝ)*M := by
        have hn : 3*J ≤ 2*M := by dsimp only [J,M]; omega
        have hr : (3:ℝ)*J ≤ 2*M := by exact_mod_cast hn
        linarith only [hr]
      have hpow : 2*(J:ℝ)^3 ≤ (M:ℝ)^3 := by
        have hh := pow_le_pow_left₀ (Nat.cast_nonneg J) hrat 3
        linarith only [hh,pow_nonneg (Nat.cast_nonneg (α := ℝ) M) 3]
      have hlog := conductorLog_mono hJ hJM.le
      have hJlog := zero_le_one.trans (conductorLog_one_le J)
      have hprior := ih J hJM
      have hlast := hoct hJM.le hMJ
      change |∑ n ∈ Ioc J M, f n| ≤ _ at hlast
      change |∑ n ∈ Ioc 0 M, f n| ≤ _
      rw [←sum_Ioc_consecutive f (Nat.zero_le J) hJM.le]
      apply (abs_add_le _ _).trans ((add_le_add hprior hlast).trans _)
      calc _ ≤ C*(J:ℝ)^3*conductorLog J+C*(J:ℝ)^3*conductorLog J := by
               exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
                 (mul_le_mul_of_nonneg_right hBC (pow_nonneg (Nat.cast_nonneg J) 3)) hJlog)
           _ = C*(2*(J:ℝ)^3)*conductorLog J := by ring
           _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hlog hJlog
             (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg M) 3))

#print axioms seventeenNinths_to_nineteenTenths_prefix
#print axioms nineteen_tenths_shell_partial_octave
#print axioms capped_shell_to_nineteen_tenths
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
