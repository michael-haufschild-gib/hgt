import GaloisForLFunctions.SignedArithmeticCorrespondences.WeilMassOnDilatedCombWindows
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTwistedDensityOfTheCarrierIsWeilsSymbol

/-!
# The spacing threshold for divergent Weil mass floors

The flat divisor on the whole dyadic window has a finite unit-spacing
Rayleigh limit. Every fixed-ratio window containing it therefore has an
upper bound on its uniform floor. At every larger integer spacing the
floor tends to infinity even on arbitrary subcombs.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology HodgeTheoryOfAFixedPart
open AbsoluteGeometryOfSpecZ (harm harm_le_one_add_log flatPairing flatPairing_self flatPacket jetKernel stepPacket
  packetForm_flatPacket_eq tendsto_combForm_blockFunction_div tendsto_riemannSum_of_continuousOn_Ioc)
open scoped ArithmeticFunction.vonMangoldt

/-- Exact dilation law for the whole square. The part with no reciprocal
spacing is the diagonal minus prime incidence. The pole plane and real
jets occur with the same factor as the base square. -/
theorem full_comb_dilation (d : ℕ+) (S : Finset ℕ) (hS : ∀ n ∈ S, 0<n) (c : ℕ → ℝ) :
    let f := fun n => (d:ℕ)*n
    let u := fun n => c (f n)
    let D := ∑ n ∈ S, u n^2*counterterm n
    let P := ∑ n ∈ S, ∑ m ∈ S.erase n, u m*u n*HodgeTheoryOfAFixedPart.contact m n
    combForm (S.image f) c = combForm S u/(d:ℝ)+(1-1/(d:ℝ))*(D-P)+
      (∑ n ∈ S, u n^2)*Real.log d := by
  intro f u D P
  have hf : Function.Injective f := fun _ _ e => Nat.eq_of_mul_eq_mul_left d.pos e
  have hs (T : Finset ℕ) (h : ℕ → ℝ) : ∑ i ∈ T.image f, h i = ∑ j ∈ T, h (f j) :=
    sum_image (fun _ _ _ _ e => hf e)
  let J := ∑ n ∈ S, ∑ m ∈ S.erase n, u m*u n*jetKernel m n
  let M := ∑ n ∈ S, u n^2
  have hbase : combPairing S u = J+P-D := by
    simp only [combPairing,pairKernel,mul_add,sum_add_distrib,J,P,D]
  have hc (m n : ℕ) : HodgeTheoryOfAFixedPart.contact (f m) (f n) =
      HodgeTheoryOfAFixedPart.contact m n := ratioContact_dilate (fun k => Λ k) d m n
  have row (n : ℕ) :
      ∑ m ∈ (S.image f).erase (f n), c m*c (f n)*pairKernel m (f n) =
        (∑ m ∈ S.erase n, u m*u n*jetKernel m n)/(d:ℝ)+
          ∑ m ∈ S.erase n, u m*u n*HodgeTheoryOfAFixedPart.contact m n := by
    rw [← image_erase hf,hs,sum_div,← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [pairKernel,hc,show jetKernel (f m) (f n)=jetKernel m n/(d:ℝ) from jetKernel_dilate d m n]
    dsimp only [u]
    ring
  have hdiag (n : ℕ) (hn : n∈S) : c (f n)^2*counterterm (f n) =
      u n^2*counterterm n+u n^2*Real.log d := by
    rw [show counterterm (f n)=counterterm n+Real.log d from counterterm_dilate d (hS n hn),mul_add]
  have hnew : combPairing (S.image f) c = J/(d:ℝ)+P-(D+M*Real.log d) := by
    simp only [combPairing,hs,row,sum_congr rfl hdiag,sum_add_distrib,J,P,D,M,sum_div,sum_mul]
  rw [combForm,combForm,hbase,hnew,pole_plane_dilate]
  change _ = _+(1-1/(d:ℝ))*(D-P)+M*Real.log d
  ring

private theorem dyadic_value :
    2*Real.log 2-(flatPairing 2 2-2*flatPairing 1 2+flatPairing 1 1) =
      3*Real.log 3-Real.log (4*Real.pi)-Real.eulerMascheroniConstant := by
  rw [flatPairing_self (a := 2) (by decide),flatPairing_self (a := 1) (by decide)]
  have hl : Real.log (4*Real.pi) = Real.log 2+Real.log (2*Real.pi) := by
    rw [show (4:ℝ)*Real.pi=2*(2*Real.pi) by ring,Real.log_mul (by norm_num) (by positivity)]
  norm_num [flatPairing]
  linarith only [hl]

/-- Rayleigh limit of the actual flat integral divisor on (N,2N]. No
prime power has a nonzero overlap on this window. -/
theorem flat_dyadic_comb_limit :
    Tendsto (fun N : ℕ => combForm (Ioc N (N+N)) (fun _ => 1)/(N:ℝ)) atTop
      (𝓝 (3*Real.log 3-Real.log (4*Real.pi)-Real.eulerMascheroniConstant)) := by
  rw [← dyadic_value]
  have h := tendsto_combForm_blockFunction_div (R := 1) (J := 1) (Q := 2)
    (by decide) (by decide) (fun _ => 1)
  have hp : stepPacket 1 1 (fun _ => 1) = flatPacket 1 2 := by
    funext x
    norm_num [stepPacket]
  have he := packetForm_flatPacket_eq (a := 1) (b := 2) (by decide) (by decide) 2
  norm_num at he
  simpa only [one_mul,mul_one,hp,he] using h

/-- For each window ratio at least two, spacing one is the unique positive
integer spacing at which uniform coefficient-mass floors cannot diverge. -/
theorem arbitrarily_large_comb_floor_iff (d Q : ℕ+) :
    (∀ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Ioc N (N+(Q:ℕ)*N) →
      ∀ c : ℕ → ℝ, let T := S.image (fun n => (d:ℕ)*n)
        B*(∑ n ∈ T, c n^2) ≤ combForm T c) ↔ 2≤(d:ℕ) := by
  refine ⟨?_,fun hd B => eventually_dilated_comb_floor d hd Q B⟩
  intro h
  by_contra! hd
  have hd₁ : (d:ℕ)=1 := by have := d.pos; omega
  let E := 3*Real.log 3-Real.log (4*Real.pi)-Real.eulerMascheroniConstant
  have hu : ∀ᶠ N : ℕ in atTop, combForm (Ioc N (N+N)) (fun _ => 1)/(N:ℝ)<E+1 :=
    flat_dyadic_comb_limit.eventually (Iio_mem_nhds (show E<E+1 by linarith))
  obtain ⟨N, hN, hlow, hhigh⟩ := ((eventually_ge_atTop 1).and ((h (E+1)).and hu)).exists
  have hs : Ioc N (N+N) ⊆ Ioc N (N+(Q:ℕ)*N) :=
    Ioc_subset_Ioc le_rfl (Nat.add_le_add_left (Nat.le_mul_of_pos_left N Q.pos) N)
  have hmass : (E+1)*(N:ℝ) ≤ combForm (Ioc N (N+N)) (fun _ => 1) := by
    simpa [hd₁,Nat.card_Ioc] using hlow (Ioc N (N+N)) hs (fun _ => 1)
  exact (not_lt_of_ge ((le_div_iff₀ (Nat.cast_pos.mpr hN : (0:ℝ)<N)).mpr hmass)) hhigh

/-- The same sharp spacing threshold holds at every fixed real aperture,
however narrow. A single flat block beginning at a sufficiently large
integer multiple of its width has a finite unit-spacing Rayleigh limit. -/
theorem divergent_comb_floor_at_any_aperture_iff (d : ℕ+) {θ : ℝ} (hθ : 0<θ) :
    (∀ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Ioc N (N+⌊θ*(N:ℝ)⌋₊) →
      ∀ c : ℕ → ℝ, let T := S.image (fun n => (d:ℕ)*n)
        B*(∑ n ∈ T, c n^2) ≤ combForm T c) ↔ 2≤(d:ℕ) := by
  constructor
  · intro h
    by_contra! hd
    have hd₁ : (d:ℕ)=1 := by have := d.pos; omega
    obtain ⟨R,hR⟩ := exists_nat_gt (1/θ)
    have hR₀ : 0<R := Nat.cast_pos.mp ((one_div_pos.mpr hθ).trans hR)
    have hRθ : 1≤θ*(R:ℝ) := by simpa only [mul_comm] using ((div_lt_iff₀ hθ).mp hR).le
    let E := AbsoluteGeometryOfSpecZ.packetForm 2 (stepPacket R 1 (fun _ => 1))
    have hi := tendsto_combForm_blockFunction_div (R := R) (J := 1) (Q := 2)
      hR₀ (by omega) (fun _ => 1)
    have hflat : Tendsto (fun n : ℕ => combForm (Ioc (R*n) (R*n+n)) (fun _ => 1)/(n:ℝ))
        atTop (𝓝 E) := by simpa only [mul_one] using hi
    obtain ⟨N₀,hfloor⟩ := eventually_atTop.mp (h (E+1))
    obtain ⟨n,⟨hn,hn₀⟩,hhi⟩ := (((eventually_ge_atTop 1).and (eventually_ge_atTop N₀)).and
      (hflat.eventually (Iio_mem_nhds (show E<E+1 by linarith)))).exists
    have hnR : N₀≤R*n := hn₀.trans (Nat.le_mul_of_pos_left n hR₀)
    have hwidth : n≤⌊θ*((R*n:ℕ):ℝ)⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_mul,← mul_assoc]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hRθ (Nat.cast_nonneg (α := ℝ) n)
    have hS : Ioc (R*n) (R*n+n) ⊆ Ioc (R*n) (R*n+⌊θ*((R*n:ℕ):ℝ)⌋₊) :=
      Ioc_subset_Ioc le_rfl (Nat.add_le_add_left hwidth _)
    have hl : (E+1)*(n:ℝ)≤combForm (Ioc (R*n) (R*n+n)) (fun _ => 1) := by
      simpa [hd₁,Nat.card_Ioc] using hfloor (R*n) hnR _ hS (fun _ => 1)
    exact (not_lt_of_ge ((le_div_iff₀ (Nat.cast_pos.mpr hn : (0:ℝ)<n)).mpr hl)) hhi
  · intro hd
    let Q : ℕ+ := ⟨⌈θ⌉₊+1,Nat.succ_pos _⟩
    have hQ : θ≤((Q:ℕ):ℝ) := (Nat.le_ceil θ).trans (Nat.cast_le.mpr (Nat.le_succ _))
    intro B
    filter_upwards [eventually_dilated_comb_floor d hd Q B] with N hN
    intro S hS c
    have hwidth : ⌊θ*(N:ℝ)⌋₊≤(Q:ℕ)*N := by
      apply (Nat.cast_le (α := ℝ)).mp
      rw [Nat.cast_mul]
      exact (Nat.floor_le (mul_nonneg hθ.le (Nat.cast_nonneg _))).trans
        (mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg _))
    exact hN S (hS.trans (Ioc_subset_Ioc le_rfl (Nat.add_le_add_left hwidth _))) c

/-- For an arbitrary sequence of window widths, unit spacing admits
divergent uniform mass floors precisely at vanishing relative width. -/
theorem divergent_unit_floor_iff_relative_width_zero (M : ℕ → ℕ) :
    (∀ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Ioc N (N+M N) → ∀ c : ℕ → ℝ,
      B*(∑ n ∈ S, c n^2) ≤ combForm S c) ↔
      Tendsto (fun N => (M N:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
  constructor
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨R,hR⟩ := exists_nat_gt (4/ε)
    have hR₀ : 0<R := Nat.cast_pos.mp ((div_pos (by norm_num) hε).trans hR)
    have h₄ : (4:ℝ)≤ε*R := by simpa only [mul_comm] using ((div_lt_iff₀ hε).mp hR).le
    let E := AbsoluteGeometryOfSpecZ.packetForm 2 (stepPacket R 1 (fun _ => 1))
    have hi := tendsto_combForm_blockFunction_div (R := R) (J := 1) (Q := 2) hR₀ (by omega) (fun _ => 1)
    have hflat : Tendsto (fun n : ℕ => combForm (Ioc (R*n) (R*n+n)) (fun _ => 1)/(n:ℝ))
        atTop (𝓝 E) := by simpa only [mul_one] using hi
    obtain ⟨T,hT⟩ := eventually_atTop.mp (hflat.eventually (Iio_mem_nhds (show E<E+1 by linarith)))
    filter_upwards [h (E+1),eventually_ge_atTop ((R+T+1)*R),eventually_ge_atTop 1] with N hfloor hN hN₁
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    by_contra! hεN
    have hnR : (0:ℝ)<N := Nat.cast_pos.mpr hN₁
    have hwide := (le_div_iff₀ hnR).mp hεN
    have harea : 4*N≤R*M N := by
      exact_mod_cast (calc (4:ℝ)*N ≤ (ε*R)*N := mul_le_mul_of_nonneg_right h₄ hnR.le
                           _ = R*(ε*N) := by ring
                           _ ≤ (R:ℝ)*(M N:ℝ) := mul_le_mul_of_nonneg_left hwide (Nat.cast_nonneg _))
    let b := N/R+1
    have hq := (Nat.le_div_iff_mul_le hR₀).mpr hN
    have hb : R≤b ∧ T≤b := by dsimp [b]; omega
    have hstart : N<R*b := Nat.lt_mul_div_succ N hR₀
    have hend : R*b≤N+R := by
      dsimp only [b]
      rw [Nat.mul_add,Nat.mul_one]
      exact Nat.add_le_add_right (Nat.mul_div_le N R) R
    have hRN : R≤N := (Nat.le_mul_of_pos_left R (Nat.succ_pos _)).trans hN
    have hdouble : 2*b≤M N := by
      apply Nat.le_of_mul_le_mul_left _ hR₀
      calc R*(2*b)=2*(R*b) := by ring
           _ ≤ 4*N := by omega
           _ ≤ _ := harea
    have hS : Ioc (R*b) (R*b+b) ⊆ Ioc N (N+M N) := Ioc_subset_Ioc hstart.le (by omega)
    have hl : (E+1)*(b:ℝ)≤combForm (Ioc (R*b) (R*b+b)) (fun _ => 1) := by
      simpa [Nat.card_Ioc] using hfloor _ hS (fun _ => 1)
    have hbp : (0:ℝ)<b := Nat.cast_pos.mpr (Nat.succ_pos _)
    exact (not_lt_of_ge ((le_div_iff₀ hbp).mpr hl)) (hT b hb.2)
  · intro h B
    let L := max 0 (B+Real.log (2*Real.pi)+2*chebyshev 2+2)
    let t := Real.exp L
    have ht : 0<t := Real.exp_pos _
    have ht₁ : 1≤t := Real.one_le_exp (le_max_left _ _)
    filter_upwards [h.eventually (Iio_mem_nhds (one_div_pos.mpr ht)),eventually_ge_atTop 1] with N hsmall hN
    intro S hs c
    have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
    have hm : (M N:ℝ)*t ≤ N := by
      have hh := (div_lt_div_iff₀ hn ht).mp hsmall
      simpa only [one_mul] using hh.le
    have hle : (M N:ℝ)≤N := (le_mul_of_one_le_right (Nat.cast_nonneg _) ht₁).trans hm
    have hleN : M N≤N := Nat.cast_le.mp hle
    rcases Nat.eq_zero_or_pos (M N) with hzero | hpos
    · have hempty : S=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn'
        have hh := mem_Ioc.mp (hs hn')
        omega
      simp [hempty,combForm,combPairing,degOne,degTwo]
    have hmr : (0:ℝ)<M N := Nat.cast_pos.mpr hpos
    have hlog := Real.log_le_log (mul_pos hmr ht) hm
    rw [Real.log_mul hmr.ne' ht.ne',show Real.log t=L from Real.log_exp _] at hlog
    have hc₁ : (M N:ℝ)/(4*N)≤1/4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [hle]
    have hc₂ : (M N:ℝ)^3/(2*(N:ℝ)^3)≤1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [pow_le_pow_left₀ hmr.le hle 3]
    have hL := le_max_right (0:ℝ) (B+Real.log (2*Real.pi)+2*chebyshev 2+2)
    change _ ≤ L at hL
    have hbound : B≤counterterm N-2*chebyshev 2-(harm (M N)+(M N:ℝ)/(4*N)+(M N:ℝ)^3/(2*(N:ℝ)^3)) := by
      rw [counterterm,Real.log_div hn.ne' (by positivity)]
      linarith only [hL,hlog,harm_le_one_add_log (M N),hc₁,hc₂]
    apply (mul_le_mul_of_nonneg_right hbound (sum_nonneg fun _ _ => sq_nonneg _)).trans
    simpa using dilated_comb_floor (1:ℕ+) hN (Q := 2) (by omega) hs c

private theorem mean_dyadic_diagonal :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc N (N+N), counterterm n)/(N:ℝ)-Real.log N) atTop
      (𝓝 (2*Real.log 2-1-Real.log (2*Real.pi))) := by
  let g := fun y : ℝ => Real.log (1+y)
  have hg : ContinuousOn g (Set.Ioc 0 1) :=
    (continuous_const.add continuous_id).continuousOn.log (fun y hy => by
      change 1+y≠0
      linarith only [hy.1])
  have hbound (y : ℝ) (hy : y∈Set.Ioc 0 1) : |g y|≤Real.log 2 := by
    change |Real.log (1+y)|≤_
    rw [abs_of_nonneg (Real.log_nonneg (by linarith only [hy.1]))]
    exact Real.log_le_log (by linarith only [hy.1]) (by linarith only [hy.2])
  have hI : (∫ y in (0:ℝ)..1, g y)=2*Real.log 2-1 := by
    dsimp only [g]
    rw [intervalIntegral.integral_comp_add_left,integral_log]
    norm_num
    ring
  have hl := tendsto_riemannSum_of_continuousOn_Ioc hg hbound
  rw [hI] at hl
  apply (hl.sub_const (Real.log (2*Real.pi))).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpos : (0:ℝ)<N := Nat.cast_pos.mpr hN
  let f := fun k : ℕ => N+(k+1)
  have hs : Ioc N (N+N)=(range N).image f := by
    ext j
    simp only [mem_Ioc,mem_image,mem_range,f]
    constructor
    · intro h
      exact ⟨j-(N+1),by omega,by omega⟩
    · rintro ⟨k,hk,rfl⟩
      omega
  have hentry (k : ℕ) : counterterm (f k)=Real.log N+g (((k:ℝ)+1)/N)-Real.log (2*Real.pi) := by
    dsimp only [counterterm,f,g]
    push_cast
    rw [Real.log_div (by positivity) (by positivity),
      show (N:ℝ)+((k:ℝ)+1)=N*(1+((k:ℝ)+1)/N) by field_simp,
      Real.log_mul hpos.ne' (by positivity)]
  rw [hs,sum_image (fun _ _ _ _ h => by dsimp only [f] at h; omega)]
  simp only [hentry,sum_sub_distrib,sum_add_distrib,sum_const,card_range,nsmul_eq_mul]
  field_simp
  ring

private theorem dyadic_contact_zero {N m n : ℕ} (hm : m∈Ioc N (N+N)) (hn : n∈Ioc N (N+N))
    (he : m≠n) : HodgeTheoryOfAFixedPart.contact m n=0 := by
  have hd {a b : ℕ} (ha : a∈Ioc N (N+N)) (hb : b∈Ioc N (N+N)) (hne : a≠b) : ¬a∣b := by
    rintro ⟨k,hk⟩
    obtain ⟨ha₁,ha₂⟩ := mem_Ioc.mp ha
    obtain ⟨hb₁,hb₂⟩ := mem_Ioc.mp hb
    have hk₀ : k≠0 := fun h => by simp [h] at hk; omega
    have hk₁ : k≠1 := fun h => hne (by simpa [h] using hk.symm)
    have hh := Nat.mul_le_mul_left a (show 2≤k by omega)
    omega
  simp [HodgeTheoryOfAFixedPart.contact,hd hm hn he,hd hn hm he.symm]

/-- Flat integral combs attain the leading logarithmic floor at every
spacing; the residual has an explicit finite limit. -/
theorem flat_dilated_comb_finite_part (d : ℕ+) :
    Tendsto (fun N : ℕ => combForm ((Ioc N (N+N)).image (fun n => (d:ℕ)*n)) (fun _ => 1)/(N:ℝ)-
      (1-1/(d:ℝ))*Real.log N) atTop
      (𝓝 ((3*Real.log 3-Real.log (4*Real.pi)-Real.eulerMascheroniConstant)/(d:ℝ)+
        (1-1/(d:ℝ))*(2*Real.log 2-1-Real.log (2*Real.pi))+Real.log d)) := by
  apply (((flat_dyadic_comb_limit.div_const (d:ℝ)).add
    (mean_dyadic_diagonal.const_mul (1-1/(d:ℝ)))).add_const (Real.log d)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  let S := Ioc N (N+N)
  have hP : (∑ n ∈ S, ∑ m ∈ S.erase n, HodgeTheoryOfAFixedPart.contact m n)=0 :=
    sum_eq_zero fun n hn => sum_eq_zero fun m hm => dyadic_contact_zero (mem_of_mem_erase hm) hn (mem_erase.mp hm).1
  have hmass : (S.card:ℝ)=N := by simp [S,Nat.card_Ioc]
  have h := full_comb_dilation d S (fun n hn => (Nat.zero_le N).trans_lt (mem_Ioc.mp hn).1) (fun _ => 1)
  simp only [one_mul,one_pow,hP,sub_zero,sum_const,nsmul_eq_mul,mul_one,hmass] at h
  rw [h]
  have hn : (N:ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hd : (d:ℝ)≠0 := (Nat.cast_pos.mpr d.pos).ne'
  field_simp
  ring

#print axioms divergent_unit_floor_iff_relative_width_zero
#print axioms divergent_comb_floor_at_any_aperture_iff
#print axioms flat_dilated_comb_finite_part
#print axioms flat_dyadic_comb_limit
#print axioms full_comb_dilation
#print axioms arbitrarily_large_comb_floor_iff
end GaloisForLFunctions.SignedArithmeticCorrespondences
