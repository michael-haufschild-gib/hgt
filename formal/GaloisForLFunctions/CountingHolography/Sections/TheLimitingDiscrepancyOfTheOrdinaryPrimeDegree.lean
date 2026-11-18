import GaloisForLFunctions.CountingHolography.Sections.TheProperPrimePowersOnAMovingSquare
import GaloisForLFunctions.CountingHolography.Sections.OriginalSectionsAtDiagonalMultiplicity
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity

/-!
# The ordinary-prime contact and the signed square degree

The two long lags share the same proper-power limit. The short contacts
have fixed finite support. Along all integer conductors the proper powers
and the real-place jet therefore each contribute a fixed constant.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticFunction ArithmeticWeightTheory ArithmeticCastelnuovoSeveri
open BiScaleUncertainty.ChebyshevGauge ArithmeticScatteringHolography _root_.RHTower.WeilDeletion

private abbrev D := successorSquareTriple
private abbrev P (k : ℕ) : ℝ := if k.Prime then 0 else vonMangoldt k
private abbrev H := splineAutoCorr
private abbrev X (n : ℕ) := (n:ℝ)^2
private abbrev Y (n : ℕ) := (((2*n+1:ℕ):ℝ)^2)
private abbrev L (n : ℕ) := 3*windowEnd ((2*n+1)^2+1)
private abbrev cutoff := ⌈Real.exp (9+Real.log 9)⌉₊

private def longRow (B : ℝ) (k : ℕ) := (2/Real.sqrt k)*H (Real.log B-Real.log k)*P k
private def shortRow (δ : ℝ) (k : ℕ) :=
  (2/Real.sqrt k)*(6*H (-Real.log k)-2*H (-Real.log k+δ)-2*H (-Real.log k-δ))*P k

/-- Evaluate the nine atom pairs without any restriction on the prime exponent. -/
private theorem contact_rows {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hs : 8 < Real.log (X n)) :
    integratedContact (D n) k*P k =
      shortRow (Real.log (Y n)-Real.log (X n)) k+2*longRow (X n) k-longRow (Y n) k := by
  let s := Real.log (X n)
  let t := Real.log (Y n)
  let l := Real.log k
  have hsum (F : ℝ → ℝ) : (∑ i, ((D n i):ℝ)*F ((i:ℝ)+1)) = F 1+2*F (X n)-F (Y n) := by
    calc _ = ∑ i : Fin ((2*n+1)^2+1), F ((i:ℝ)+1)*((D n i):ℝ) :=
                sum_congr rfl fun _ _ => mul_comm _ _
         _ = _ := sum_successorSquareTriple hn F
  have hrow (i : Fin ((2*n+1)^2+1)) :
      (∑ j, ((D n i):ℝ)*((D n j):ℝ)*H (-l-Real.log ((i:ℝ)+1)+Real.log ((j:ℝ)+1))) =
      ((D n i):ℝ)*(H (-l-Real.log ((i:ℝ)+1))+2*H (-l-Real.log ((i:ℝ)+1)+s)-H (-l-Real.log ((i:ℝ)+1)+t)) := by
    simp_rw [mul_assoc]
    rw [← mul_sum,hsum (fun v => H (-l-Real.log ((i:ℝ)+1)+Real.log v))]
    simp only [Real.log_one,add_zero,s,t]
  have hxy : X n ≤ Y n := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2
  have ht : s ≤ t := Real.log_le_log (sq_pos_of_pos (Nat.cast_pos.mpr hn)) hxy
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hk)
  have hz (u : ℝ) (hu : 8 < u) : H (-l-u)=0 :=
    splineAutoCorr_zero_outside (lt_abs.mpr (Or.inr (by linarith only [hu,hl])))
  rw [integratedContact_eq_autocorrelations]
  change (2/Real.sqrt k)*(∑ i, ∑ j, ((D n i):ℝ)*((D n j):ℝ)*
    H (-l-Real.log ((i:ℝ)+1)+Real.log ((j:ℝ)+1)))*P k=_
  simp_rw [hrow]
  rw [hsum (fun v => H (-l-Real.log v)+2*H (-l-Real.log v+s)-H (-l-Real.log v+t))]
  simp only [Real.log_one,sub_zero]
  change (2/Real.sqrt k)*((H (-l)+2*H (-l+s)-H (-l+t))+
    2*(H (-l-s)+2*H (-l-s+s)-H (-l-s+t))-(H (-l-t)+2*H (-l-t+s)-H (-l-t+t)))*P k=_
  rw [hz s hs,hz t (hs.trans_le ht)]
  dsimp only [shortRow,longRow]
  change _=(2/Real.sqrt k)*(6*H (-l)-2*H (-l+(t-s))-2*H (-l-(t-s)))*P k+
    2*((2/Real.sqrt k)*H (s-l)*P k)-(2/Real.sqrt k)*H (t-l)*P k
  rw [show -l-s+t= -l+(t-s) by ring,show -l-t+s= -l-(t-s) by ring,
    show -l+s=s-l by ring,show -l+t=t-l by ring,sub_add_cancel,sub_add_cancel]
  ring

private theorem longRow_sum {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : ⌊Real.exp 8*B⌋₊ ≤ N) :
    ∑ k ∈ Ioc 0 N, longRow B k = longProperPowerContact B := by
  unfold longProperPowerContact
  have hsub : Ioc ⌊Real.exp (-9)*B⌋₊ ⌊Real.exp 8*B⌋₊ ⊆ Ioc 0 N := by
    intro k hk
    exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2.trans hN⟩
  apply (sum_subset (f := longRow B) hsub ?_).symm
  · intro k hk hbad
    have hk₀ : (0:ℝ) < k := Nat.cast_pos.mpr (mem_Ioc.mp hk).1
    have harg : 8 < |Real.log B-Real.log k| := by
      by_cases hlo : ⌊Real.exp (-9)*B⌋₊ < k
      · have hhi : ⌊Real.exp 8*B⌋₊ < k := lt_of_not_ge fun hh => hbad (mem_Ioc.mpr ⟨hlo,hh⟩)
        have hkn : ⌊Real.exp 8*B⌋₊+1 ≤ k := Nat.succ_le_of_lt hhi
        have hp : Real.exp 8*B < (k:ℝ) := (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hkn)
        have h := Real.log_lt_log (mul_pos (Real.exp_pos _) hB) hp
        rw [Real.log_mul (Real.exp_pos _).ne' hB.ne',Real.log_exp] at h
        exact lt_abs.mpr (Or.inr (by linarith only [h]))
      · have hp : (k:ℝ) ≤ Real.exp (-9)*B := (Nat.cast_le.mpr (le_of_not_gt hlo)).trans (Nat.floor_le (by positivity))
        have h := Real.log_le_log hk₀ hp
        rw [Real.log_mul (Real.exp_pos _).ne' hB.ne',Real.log_exp] at h
        exact lt_abs.mpr (Or.inl (by linarith only [h]))
    change (2/Real.sqrt k)*splineAutoCorr (Real.log B-Real.log k)*P k=0
    rw [splineAutoCorr_zero_outside harg,mul_zero,zero_mul]

private theorem shortRow_support {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ Real.log 9) {k : ℕ}
    (hk : cutoff < k) : shortRow δ k=0 := by
  have hk' : Real.exp (9+Real.log 9) < (k:ℝ) := (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr hk)
  have h := Real.log_lt_log (Real.exp_pos _) hk'
  rw [Real.log_exp] at h
  have hz {u : ℝ} (hu : u < -8) : H u=0 := splineAutoCorr_zero_outside (lt_abs.mpr (Or.inr (by linarith only [hu])))
  have h₀ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 9)
  unfold shortRow
  rw [hz (u := -Real.log k) (by linarith only [h,h₀]),
    hz (u := -Real.log k+δ) (by linarith only [h,hδ]),
    hz (u := -Real.log k-δ) (by linarith only [h,h₀,hδ₀])]
  ring

private abbrev shift (n : ℕ) := Real.log (Y n)-Real.log (X n)

private theorem shift_limit : Tendsto shift atTop (𝓝 (Real.log 4)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have h := (hi.const_add 2).pow 2
  norm_num at h
  apply ((Real.continuousAt_log (by norm_num : (4:ℝ) ≠ 0)).tendsto.comp h).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn₀ : (0:ℝ) < n := Nat.cast_pos.mpr hn
  change Real.log ((2+(n:ℝ)⁻¹)^2)=Real.log (Y n)-Real.log (X n)
  rw [← Real.log_div (sq_pos_of_pos (by positivity)).ne' (sq_pos_of_pos hn₀).ne']
  apply congrArg Real.log
  change (2+(n:ℝ)⁻¹)^2=(((2*n+1:ℕ):ℝ)^2)/(n:ℝ)^2
  push_cast
  field_simp [hn₀.ne']

private theorem proper_sum (n : ℕ) :
    fullPrimeContact (D n)-ordinaryPrimeContact (D n)=
      ∑ k ∈ Ioc 0 (L n), integratedContact (D n) k*P k := by
  unfold fullPrimeContact ordinaryPrimeContact ordinaryPrimeLags
  rw [sum_filter,← sum_sub_distrib]
  have h : ∑ k ∈ Icc 2 (L n), (integratedContact (D n) k*vonMangoldt k-
      (if k.Prime then integratedContact (D n) k*vonMangoldt k else 0)) =
      ∑ k ∈ Icc 2 (L n), integratedContact (D n) k*P k := by
    apply sum_congr rfl
    intro k _
    by_cases hp : k.Prime <;> simp [P,hp]
  rw [h]
  apply sum_subset
  · exact fun k hk => mem_Ioc.mpr ⟨by have := (mem_Icc.mp hk).1; omega,(mem_Icc.mp hk).2⟩
  · intro k hk hbad
    have he : k=1 := by
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hk
      by_contra! hne
      exact hbad (mem_Icc.mpr ⟨by omega,hu⟩)
    simp [he,P]

/-- On every sufficiently large conductor the proper powers split
exactly into one fixed finite short sum and the two moving long lags. -/
private theorem proper_split : ∀ᶠ n : ℕ in atTop,
    fullPrimeContact (D n)-ordinaryPrimeContact (D n) =
      (∑ k ∈ Ioc 0 cutoff, shortRow (shift n) k)+2*longProperPowerContact (X n)-longProperPowerContact (Y n) := by
  have hX : Tendsto X atTop atTop := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  have harg := (Real.tendsto_log_atTop.comp hX).eventually_gt_atTop 8
  have h₄ : (0:ℝ)<Real.log 4 := Real.log_pos (by norm_num)
  have h₉ := Real.log_lt_log (by norm_num : (0:ℝ)<4) (by norm_num : (4:ℝ)<9)
  filter_upwards [eventually_ge_atTop 1,harg,hX.eventually_ge_atTop (cutoff:ℝ),
    shift_limit.eventually_const_le h₄,shift_limit.eventually_le_const h₉] with n hn hs hcut hδ₀ hδ
  let N := L n
  let win := windowEnd ((2*n+1)^2+1)
  have hxy : X n ≤ Y n := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2
  have hw : Real.exp 8*Y n ≤ (win:ℝ) := (successorSquareWindowScale_bounds n).2.2
  have hwin : win ≤ N := by dsimp only [N,L,win]; omega
  have hcap := hw.trans (Nat.cast_le.mpr hwin)
  have hfloor {B : ℝ} (hb₀ : 0 ≤ B) (hb : B ≤ Y n) : ⌊Real.exp 8*B⌋₊ ≤ N := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hb₀)).trans
      ((mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans hcap)
  have hN : cutoff ≤ N := Nat.cast_le.mp (hcut.trans ((successorSquareWindowScale_bounds n).1.trans hcap))
  have hshort : ∑ k ∈ Ioc 0 N, shortRow (shift n) k=∑ k ∈ Ioc 0 cutoff, shortRow (shift n) k := by
    apply (sum_subset (fun k hk => mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2.trans hN⟩) ?_).symm
    intro k hk hbad
    exact shortRow_support hδ₀ hδ (lt_of_not_ge fun hh => hbad (mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,hh⟩))
  rw [proper_sum]
  change (∑ k ∈ Ioc 0 N, integratedContact (D n) k*P k)=_
  have hrow {k : ℕ} (hk : k ∈ Ioc 0 N) :
      integratedContact (D n) k*P k=shortRow (shift n) k+2*longRow (X n) k-longRow (Y n) k :=
    contact_rows hn (mem_Ioc.mp hk).1 hs
  rw [sum_congr rfl (fun k hk => hrow hk),
    sum_sub_distrib,sum_add_distrib,← mul_sum,hshort,
    longRow_sum (sq_pos_of_pos (Nat.cast_pos.mpr hn)) (hfloor (sq_nonneg _) hxy),
    longRow_sum (sq_pos_of_pos (by positivity : (0:ℝ)<((2*n+1:ℕ):ℝ))) (hfloor (sq_nonneg _) le_rfl)]

/-- The two forward lags contribute one unit in total. The finite short
contact is evaluated at the limiting separation log four. -/
def squareProperPowerConstant : ℝ := (∑ k ∈ Ioc 0 cutoff, shortRow (Real.log 4) k)+1

/-- The proper powers have a common finite limiting contribution on all
square conductors. Their short rows converge term by term and the two
long rows see the same square-root density. -/
theorem successorSquare_proper_power_contact_limit :
    Tendsto (fun n => fullPrimeContact (D n)-ordinaryPrimeContact (D n)) atTop (𝓝 squareProperPowerConstant) := by
  have hc := longProperPowerContact_limit
  have hX : Tendsto X atTop atTop := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  have hY : Tendsto Y atTop atTop := tendsto_atTop_mono (fun n => pow_le_pow_left₀ (Nat.cast_nonneg n)
    (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2) hX
  have hshort (k : ℕ) : Continuous (fun δ => shortRow δ k) := by
    have hp : Continuous (fun δ : ℝ => H (-Real.log k+δ)) :=
      continuous_splineAutoCorr.comp (continuous_const.add continuous_id)
    have hm : Continuous (fun δ : ℝ => H (-Real.log k-δ)) :=
      continuous_splineAutoCorr.comp (continuous_const.sub continuous_id)
    unfold shortRow
    exact (continuous_const.mul ((continuous_const.sub (continuous_const.mul hp)).sub
      (continuous_const.mul hm))).mul continuous_const
  have hfin := tendsto_finsetSum (Ioc 0 cutoff) fun k _ => (hshort k).continuousAt.tendsto.comp shift_limit
  rw [show squareProperPowerConstant=(∑ k ∈ Ioc 0 cutoff, shortRow (Real.log 4) k)+2*1-1 by
    unfold squareProperPowerConstant; ring]
  exact ((hfin.add ((hc.comp hX).const_mul 2)).sub (hc.comp hY)).congr'
    (proper_split.mono fun _ h => h.symm)

/-- The integrated ordinary prime contact differs from the negative signed
Weil degree by a single limiting constant through every square conductor. -/
theorem successorSquare_ordinary_contact_discrepancy_limit :
    ∃ b : ℝ, Tendsto (fun n => ordinaryPrimeContact (D n)+integerProbe _ (D n)) atTop (𝓝 b) := by
  have hc := successorSquare_proper_power_contact_limit
  obtain ⟨z,hz⟩ := successorSquare_archimedean_jet_limit
  have h := ((successorSquare_jet_discrepancy id id tendsto_id tendsto_id).sub
    (hz id id tendsto_id tendsto_id)).sub hc
  refine ⟨_,h.congr fun n => ?_⟩
  change (_+(integerProbe _ (D n)+fullPrimeContact (D n))-_)-(fullPrimeContact (D n)-ordinaryPrimeContact (D n))=_
  ring

/-- Linear mesh error divided by m² costs at most C/n simultaneously for
every m at or above the conductor index. -/
private theorem normalized_mesh_error {C P g : ℝ} {n m : ℕ} (hC : 0 ≤ C) (hn : 0 < n) (hm : n ≤ m)
    (h : |g-(m:ℝ)^2*P| ≤ C*n) : |g/(m:ℝ)^2-P| ≤ C/n := by
  have hn₀ : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hm₀ : (0:ℝ) < m := Nat.cast_pos.mpr (hn.trans_le hm)
  have hsq := pow_le_pow_left₀ hn₀.le (Nat.cast_le.mpr hm) 2
  rw [show g/(m:ℝ)^2-P=(g-(m:ℝ)^2*P)/(m:ℝ)^2 by field_simp [hm₀.ne'],
    abs_div,abs_of_nonneg (sq_nonneg (m:ℝ))]
  calc _ ≤ C*n/(m:ℝ)^2 := div_le_div_of_nonneg_right h (sq_nonneg _)
    _ ≤ C/n := (div_le_div_iff₀ (sq_pos_of_pos hm₀) hn₀).mpr (by
      linarith only [mul_le_mul_of_nonneg_left hsq hC])

/-- At every multiplicity above the diagonal, both the actual excess of
the full log ideal over its ordinary part and the compensated ordinary
log ideal have common limits, uniformly in the multiplicity. -/
theorem square_prime_generator_discrepancies_above_diagonal :
    ∃ b : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m →
      let a := m • successorSquareTriple n
      |(Real.log (generator a:ℝ)-Real.log (ordinaryPrimeGenerator a:ℝ))/(m:ℝ)^2-squareProperPowerConstant| ≤ ε ∧
      |(Real.log (ordinaryPrimeGenerator a:ℝ)+ordinaryFloorLoss a)/(m:ℝ)^2+
        integerProbe _ (successorSquareTriple n)-b| ≤ ε := by
  let c := squareProperPowerConstant
  have hc := successorSquare_proper_power_contact_limit
  obtain ⟨b,hb⟩ := successorSquare_ordinary_contact_discrepancy_limit
  obtain ⟨F,hF,hfull⟩ := successorSquare_full_generator_error
  obtain ⟨O,hO,hord⟩ := successorSquare_floor_corrected_mesh_error
  let C := F+O
  have hC : 0 ≤ C := add_nonneg hF hO
  have ht : Tendsto (fun n : ℕ => C/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨b,fun ε hε => ?_⟩
  have hc' := (hc.sub_const squareProperPowerConstant).abs
  have hb' := (hb.sub_const b).abs
  simp only [sub_self,abs_zero] at hc' hb'
  filter_upwards [eventually_ge_atTop 1,ht.eventually_le_const (half_pos hε),
    hc'.eventually_le_const (half_pos hε),hb'.eventually_le_const (half_pos hε)] with n hn hsmall hpc hqb m hm
  let a := m • D n
  let f := Real.log (generator a:ℝ)
  let o := Real.log (ordinaryPrimeGenerator a:ℝ)
  let V := ordinaryFloorLoss a
  let Pf := fullPrimeContact (D n)
  let Po := ordinaryPrimeContact (D n)
  let Q := integerProbe _ (D n)
  let t := (m:ℝ)^2
  have hf : |f+V-t*Pf| ≤ F*n := hfull hn m
  have ho : |o+V-t*Po| ≤ O*n := hord hn m
  have hd : |(f-o)-t*(Pf-Po)| ≤ C*n := by
    rw [show (f-o)-t*(Pf-Po)=(f+V-t*Pf)-(o+V-t*Po) by ring]
    have h := abs_sub_le (f+V-t*Pf) 0 (o+V-t*Po)
    simp only [sub_zero,zero_sub,abs_neg] at h
    dsimp only [C]; linarith only [h,hf,ho]
  have h₁ := normalized_mesh_error hC hn hm hd
  have h₂ := normalized_mesh_error hO hn hm ho
  have hscale : O/(n:ℝ) ≤ C/n := div_le_div_of_nonneg_right (by dsimp only [C]; linarith only [hF]) (Nat.cast_nonneg _)
  change |Pf-Po-c| ≤ ε/2 at hpc
  change |Po+Q-b| ≤ ε/2 at hqb
  change |(f-o)/t-c| ≤ ε ∧ |(o+V)/t+Q-b| ≤ ε
  constructor
  · rw [show (f-o)/t-c=((f-o)/t-(Pf-Po))+(Pf-Po-c) by ring]
    exact (abs_add_le _ _).trans (by linarith only [h₁,hsmall,hpc])
  · rw [show (o+V)/t+Q-b=((o+V)/t-Po)+(Po+Q-b) by ring]
    exact (abs_add_le _ _).trans (by linarith only [h₂,hscale,hsmall,hqb])

#print axioms square_prime_generator_discrepancies_above_diagonal
#print axioms successorSquare_proper_power_contact_limit
#print axioms successorSquare_ordinary_contact_discrepancy_limit

end GaloisForLFunctions.CountingHolography.Sections
