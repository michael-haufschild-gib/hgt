import GaloisForLFunctions.RHTower.RoutePHyperbolicPairDeletion
import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation

/-!
# Quadratic payment of the complete native lcm sector

Complete lcm fibres cancel every single-coordinate Möbius profile term.
Centering at the actual unit channel leaves a product of two profile errors.
The gcd map counts their common scales and supplies a convergent double
p-series majorant. This pays all pairs with lcm(d,e)<=M at the native M^2
scale, including every diagonal and common-divisor class. The exact partition
retains the complementary lcm sector; its critical bound is still open.
-/

noncomputable section
open Finset
namespace RHTower
namespace RoutePLcm

private def sector (M : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.lcm p.1 p.2 ≤ M), f p.1 p.2

private lemma divisor_filter (M q : ℕ) (hq : 0<q) (hqM : q≤M) :
    (Icc 1 M).filter (fun d => d∣q) = q.divisors := by
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_,_⟩,hd⟩
    exact ⟨hd,by omega⟩
  · rintro ⟨hd,_⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hq,(Nat.le_of_dvd hq hd).trans hqM⟩,hd⟩

private lemma single_coordinate_fibre (M n : ℕ) (hn : 0<n) (hnM : n≤M)
    (f : ℕ → ℝ) :
    finiteLcmPairCrossFibre (Icc 1 M)
      (fun d => (ArithmeticFunction.moebius d:ℝ)*f d)
      (fun e => (ArithmeticFunction.moebius e:ℝ)) n =
        (ArithmeticFunction.moebius n:ℝ)*f 1 := by
  classical
  rw [← finiteLcmPairCrossFibre_moebius_inversion _ _ _ _ hn]
  have hM : 1≤M := hn.trans_le hnM
  have hprefix : ∀ q, 0<q → q≤M →
      finiteDivisorFibrePrefix (Icc 1 M) (fun e => (ArithmeticFunction.moebius e:ℝ)) q =
        if q=1 then 1 else 0 := by
    intro q hq hqM
    rw [finiteDivisorFibrePrefix,divisor_filter M q hq hqM]
    exact Sieve.sum_divisors_moebius_real q
  rw [sum_eq_single (n,1)]
  · rw [hprefix 1 (by omega) hM]
    rw [finiteDivisorFibrePrefix,divisor_filter M 1 (by omega) hM]
    simp
  · intro z hz hne
    have hz' := Nat.mem_divisorsAntidiagonal.mp hz
    have hz2 : 0<z.2 := by nlinarith [hz'.1]
    have hz1 : 0<z.1 := by nlinarith [hz'.1]
    have hz2n : z.2≤n := by nlinarith [hz'.1]
    have hz21 : z.2≠1 := by
      intro heq
      apply hne
      apply Prod.ext
      · simpa [heq] using hz'.1
      · exact heq
    rw [hprefix z.2 hz2 (hz2n.trans hnM),if_neg hz21]
    ring
  · intro hnot
    exact False.elim (hnot (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp,by omega⟩))

private lemma single_coordinate_sector (M : ℕ) (f : ℕ → ℝ) :
    sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*f d*
      (ArithmeticFunction.moebius e:ℝ)) =
      f 1 * ∑ n ∈ Icc 1 M, (ArithmeticFunction.moebius n:ℝ) := by
  classical
  let s := (Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.lcm p.1 p.2≤M)
  have hmap : ∀ p∈s, Nat.lcm p.1 p.2∈Icc 1 M := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hp,hl⟩
    rcases mem_product.mp hp with ⟨hd,he⟩
    exact mem_Icc.mpr ⟨Nat.lcm_pos (mem_Icc.mp hd).1 (mem_Icc.mp he).1,hl⟩
  have hfib := sum_fiberwise_of_maps_to (s:=s) (t:=Icc 1 M)
    (g:=fun p => Nat.lcm p.1 p.2)
    (f:=fun p => (ArithmeticFunction.moebius p.1:ℝ)*f p.1*
      (ArithmeticFunction.moebius p.2:ℝ)) hmap
  change (∑ p∈s, _) = _
  rw [← hfib,mul_sum]
  apply sum_congr rfl
  intro n hn
  have hn' := mem_Icc.mp hn
  have hset : s.filter (fun p => Nat.lcm p.1 p.2=n) =
      (Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.lcm p.1 p.2=n) := by
    ext p
    simp only [s,mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,by simpa [h.2] using hn'.2⟩,h.2⟩
  rw [hset]
  exact (single_coordinate_fibre M n hn'.1 hn'.2 f).trans (mul_comm _ _)

private lemma sector_swap (M : ℕ) (f : ℕ → ℕ → ℝ) :
    sector M (fun d e => f e d) = sector M f := by
  classical
  unfold sector
  apply sum_nbij' (fun p => (p.2,p.1)) (fun p => (p.2,p.1))
  · intro p hp
    simpa only [mem_filter,mem_product,Nat.lcm_comm,and_comm,and_left_comm,and_assoc] using hp
  · intro p hp
    simpa only [mem_filter,mem_product,Nat.lcm_comm,and_comm,and_left_comm,and_assoc] using hp
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

private lemma centered_identity (M : ℕ) (f : ℕ → ℝ) :
    sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*f d*
      ((ArithmeticFunction.moebius e:ℝ)*f e)) =
      f 1^2*(∑ n∈Icc 1 M,(ArithmeticFunction.moebius n:ℝ))+
        sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*
          (ArithmeticFunction.moebius e:ℝ)*(f d-f 1)*(f e-f 1)) := by
  have hleft := single_coordinate_sector M f
  have hright := sector_swap M (fun d e =>
    (ArithmeticFunction.moebius d:ℝ)*f d*(ArithmeticFunction.moebius e:ℝ))
  have hone := single_coordinate_sector M (fun _ => (1:ℝ))
  have hexpand : sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*f d*
      ((ArithmeticFunction.moebius e:ℝ)*f e)) =
      sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*
        (ArithmeticFunction.moebius e:ℝ)*(f d-f 1)*(f e-f 1))+
      f 1*sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*f d*
        (ArithmeticFunction.moebius e:ℝ))+
      f 1*sector M (fun d e => (ArithmeticFunction.moebius e:ℝ)*f e*
        (ArithmeticFunction.moebius d:ℝ))-
      f 1^2*sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*1*
        (ArithmeticFunction.moebius e:ℝ)) := by
    unfold sector
    simp only [mul_sum,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  rw [hexpand,hright,hleft,hone]
  ring

private lemma scale_filter (M a b : ℕ) (ha : 0<a) (hb : 0<b) :
    (Icc 1 M).filter (fun g => g*a*b≤M) = Icc 1 (M/(a*b)) := by
  ext g
  simp only [mem_filter,mem_Icc]
  constructor
  · rintro ⟨⟨hg,_⟩,hgab⟩
    exact ⟨hg,(Nat.le_div_iff_mul_le (Nat.mul_pos ha hb)).mpr
      (by simpa only [Nat.mul_assoc] using hgab)⟩
  · rintro ⟨hg,hgq⟩
    have hgab := (Nat.le_div_iff_mul_le (Nat.mul_pos ha hb)).mp hgq
    refine ⟨⟨hg,hgq.trans (Nat.div_le_self M (a*b))⟩,?_⟩
    simpa only [Nat.mul_assoc] using hgab

private lemma positive_lcm_pair_bound (M : ℕ) (F : ℕ → ℕ → ℝ) (D : ℝ)
    (hD : 0≤D)
    (hbound : ∀ g a b : ℕ, 0<g → 0<a → 0<b → g*a*b≤M →
      F (g*a) (g*b) ≤ D/((a:ℝ)^((1:ℝ)/40)*(b:ℝ)^((1:ℝ)/40))) :
    sector M F ≤ D*(M:ℝ)*(∑' n:ℕ, 1/(n:ℝ)^((41:ℝ)/40))^2 := by
  classical
  let s := (Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.lcm p.1 p.2≤M)
  let t := ((Icc 1 M ×ˢ Icc 1 M) ×ˢ Icc 1 M).filter
    (fun t => t.2*t.1.1*t.1.2≤M)
  let ix (p : ℕ × ℕ) := ((p.1/Nat.gcd p.1 p.2,p.2/Nat.gcd p.1 p.2),Nat.gcd p.1 p.2)
  let w (t : (ℕ × ℕ) × ℕ) : ℝ :=
    D/((t.1.1:ℝ)^((1:ℝ)/40)*(t.1.2:ℝ)^((1:ℝ)/40))
  have hdata : ∀ p∈s, 0<(ix p).2 ∧ 0<(ix p).1.1 ∧ 0<(ix p).1.2 ∧
      (ix p).2*(ix p).1.1=p.1 ∧ (ix p).2*(ix p).1.2=p.2 ∧ ix p∈t := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hp,hl⟩
    rcases mem_product.mp hp with ⟨hd,he⟩
    rcases mem_Icc.mp hd with ⟨hd,hdM⟩
    rcases mem_Icc.mp he with ⟨he,heM⟩
    have hg := Nat.gcd_pos_of_pos_left p.2 hd
    have hgd := Nat.gcd_dvd_left p.1 p.2
    have hge := Nat.gcd_dvd_right p.1 p.2
    have ha := (Nat.one_le_div_iff hg).mpr (Nat.le_of_dvd hd hgd)
    have hb := (Nat.one_le_div_iff hg).mpr (Nat.le_of_dvd he hge)
    have hda := Nat.mul_div_cancel' hgd
    have heb := Nat.mul_div_cancel' hge
    have hcop := Nat.coprime_div_gcd_div_gcd hg
    refine ⟨hg,ha,hb,hda,heb,?_⟩
    change ((p.1/Nat.gcd p.1 p.2,p.2/Nat.gcd p.1 p.2),Nat.gcd p.1 p.2)∈t
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_product.mpr
      ⟨mem_Icc.mpr ⟨ha,(Nat.div_le_self _ _).trans hdM⟩,
       mem_Icc.mpr ⟨hb,(Nat.div_le_self _ _).trans heM⟩⟩,
      mem_Icc.mpr ⟨hg,(Nat.le_of_dvd hd hgd).trans hdM⟩⟩,?_⟩
    have heq := congrArg₂ Nat.lcm hda heb
    rw [Nat.lcm_mul_left,hcop.lcm_eq_mul] at heq
    simpa only [Nat.mul_assoc,heq] using hl
  have hinj : Set.InjOn ix s := by
    intro p hp q hq hi
    obtain ⟨_,_,_,hd,he,_⟩ := hdata p hp
    obtain ⟨_,_,_,hd',he',_⟩ := hdata q hq
    apply Prod.ext
    · rw [← hd,← hd',hi]
    · rw [← he,← he',hi]
  have hmajor : sector M F ≤ ∑ z∈t,w z := by
    change (∑ p∈s,F p.1 p.2)≤_
    calc
      _ ≤ ∑ p∈s,w (ix p) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hg,ha,hb,hd,he,ht⟩ := hdata p hp
        have h := hbound (ix p).2 (ix p).1.1 (ix p).1.2 hg ha hb (mem_filter.mp ht).2
        simpa only [hd,he,w] using h
      _ = ∑ z∈s.image ix,w z := (sum_image hinj).symm
      _ ≤ ∑ z∈t,w z := sum_le_sum_of_subset_of_nonneg
        (by intro z hz; obtain ⟨p,hp,rfl⟩ := mem_image.mp hz; exact (hdata p hp).2.2.2.2.2)
        (by intro z _ _; exact div_nonneg hD (mul_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hseries : Summable (fun n:ℕ => 1/(n:ℝ)^((41:ℝ)/40)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hpartial : (∑ n∈Icc 1 M,1/(n:ℝ)^((41:ℝ)/40)) ≤
      ∑' n:ℕ,1/(n:ℝ)^((41:ℝ)/40) :=
    hseries.sum_le_tsum _ (fun n _ => by positivity)
  have hsum : ∑ z∈t,w z ≤
      D*(M:ℝ)*(∑ n∈Icc 1 M,1/(n:ℝ)^((41:ℝ)/40))^2 := by
    change (∑ z∈((Icc 1 M ×ˢ Icc 1 M) ×ˢ Icc 1 M).filter
      (fun z => z.2*z.1.1*z.1.2≤M), w z) ≤ _
    rw [sum_filter,sum_product]
    simp only [sum_product]
    have hexp : ∀ a∈Icc 1 M, (a:ℝ)^((41:ℝ)/40) =
        (a:ℝ)*(a:ℝ)^((1:ℝ)/40) := by
      intro a ha
      have hap : (0:ℝ)<a := by exact_mod_cast (mem_Icc.mp ha).1
      rw [show (41:ℝ)/40=1+1/40 by norm_num,Real.rpow_add hap,Real.rpow_one]
    calc
      _ ≤ ∑ a∈Icc 1 M,∑ b∈Icc 1 M,
          D*(M:ℝ)*(1/(a:ℝ)^((41:ℝ)/40))*(1/(b:ℝ)^((41:ℝ)/40)) := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro b hb
        change (∑ g∈Icc 1 M,if g*a*b≤M then
          D/((a:ℝ)^((1:ℝ)/40)*(b:ℝ)^((1:ℝ)/40)) else 0) ≤ _
        rw [← sum_filter,scale_filter M a b (mem_Icc.mp ha).1 (mem_Icc.mp hb).1]
        simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
        have hab : (0:ℝ)<(a:ℝ)*(b:ℝ) := by
          exact_mod_cast Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1
        have hf : ((M/(a*b):ℕ):ℝ) ≤ (M:ℝ)/((a:ℝ)*(b:ℝ)) := by
          exact_mod_cast (Nat.cast_div_le (m:=M) (n:=a*b) (α:=ℝ))
        calc
          _ ≤ ((M:ℝ)/((a:ℝ)*(b:ℝ)))*
              (D/((a:ℝ)^((1:ℝ)/40)*(b:ℝ)^((1:ℝ)/40))) :=
            mul_le_mul_of_nonneg_right hf (by positivity)
          _ = _ := by rw [hexp a ha,hexp b hb]; ring
      _ = _ := by rw [pow_two,sum_mul_sum]; simp only [mul_sum]; ring
  exact hmajor.trans (hsum.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg (fun n _ => by positivity)) hpartial 2) (by positivity)))

private def profile (M d : ℕ) : ℝ := divisorUnsignedDilationChannel M d/Real.sqrt M

private lemma profile_ceiling (M d : ℕ) : |profile M d|≤(3/5:ℝ) := by
  by_cases hM : M=0
  · norm_num [profile,hM]
  have hm : (0:ℝ)<M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hs := Real.sqrt_pos.mpr hm
  rw [profile,abs_of_nonneg (div_nonneg
    (divisorUnsignedDilationChannel_nonneg M d) hs.le),div_le_iff₀ hs]
  exact divisorUnsignedDilationChannel_le_three_fifths_sqrt M d

private lemma mixed_profile_error :
    ∃ C : ℝ, 0≤C ∧ ∀ M g a b : ℕ, 0<g → 0<a → 0<b → g*a*b≤M →
      |profile M (g*a)-profile M 1| * |profile M (g*b)-profile M 1| ≤
        4*C^2/((a:ℝ)^((1:ℝ)/40)*(b:ℝ)^((1:ℝ)/40)) := by
  obtain ⟨C,hC,h⟩ := routeP_unsigned_profile_product_error
  refine ⟨C,hC,?_⟩
  intro M g a b hg ha hb hgab
  let c : ℝ := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4
  have herr : ∀ d e : ℕ, 0<d → 0<e → d*e≤M →
      |profile M d-profile M 1|≤2*C/(e:ℝ)^((1:ℝ)/40) := by
    intro d e hd he hde
    have heM : e≤M := (by nlinarith : e≤d*e).trans hde
    have h1 := h M d e hd he hde
    have h2 := h M 1 e (by omega) he (by simpa using heM)
    change |profile M d-c|≤_ at h1
    change |profile M 1-c|≤_ at h2
    calc
      _ = |(profile M d-c)-(profile M 1-c)| := by congr 1; ring
      _ ≤ |profile M d-c|+|profile M 1-c| := abs_sub _ _
      _ ≤ C/(e:ℝ)^((1:ℝ)/40)+C/(e:ℝ)^((1:ℝ)/40) := add_le_add h1 h2
      _ = _ := by ring
  have hleft := herr (g*a) b (Nat.mul_pos hg ha) hb hgab
  have hright := herr (g*b) a (Nat.mul_pos hg hb) ha (by nlinarith [hgab])
  calc
    _ ≤ (2*C/(b:ℝ)^((1:ℝ)/40))*(2*C/(a:ℝ)^((1:ℝ)/40)) :=
      mul_le_mul hleft hright (abs_nonneg _) (by positivity)
    _ = _ := by ring

private lemma moebius_ceiling (n : ℕ) : |(ArithmeticFunction.moebius n:ℝ)|≤1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=n)

private lemma normalized_sector_bound :
    ∃ B : ℝ, 0≤B ∧ ∀ M : ℕ,
      |sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*profile M d*
        ((ArithmeticFunction.moebius e:ℝ)*profile M e))| ≤ B*M := by
  obtain ⟨C,hC,herror⟩ := mixed_profile_error
  let S : ℝ := ∑' n:ℕ,1/(n:ℝ)^((41:ℝ)/40)
  refine ⟨(3/5)^2+4*C^2*S^2,by positivity,?_⟩
  intro M
  have hmu : |∑ n∈Icc 1 M,(ArithmeticFunction.moebius n:ℝ)|≤M := by
    calc
      _ ≤ ∑ n∈Icc 1 M,|(ArithmeticFunction.moebius n:ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n∈Icc 1 M,(1:ℝ) := sum_le_sum (fun n _ => moebius_ceiling n)
      _ = _ := by simp
  have hmain : |profile M 1^2*(∑ n∈Icc 1 M,(ArithmeticFunction.moebius n:ℝ))| ≤
      (3/5:ℝ)^2*M := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (profile_ceiling M 1) 2)
      hmu (abs_nonneg _) (by positivity)
  have habs : |sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*
        (ArithmeticFunction.moebius e:ℝ)*(profile M d-profile M 1)*(profile M e-profile M 1))| ≤
      sector M (fun d e => |profile M d-profile M 1| * |profile M e-profile M 1|) := by
    unfold sector
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro p _
    simp only [abs_mul]
    have hprod : |(ArithmeticFunction.moebius p.1:ℝ)| *
        |(ArithmeticFunction.moebius p.2:ℝ)|≤1 := by
      simpa only [one_mul] using mul_le_mul (moebius_ceiling p.1) (moebius_ceiling p.2)
        (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    calc
      _ ≤ 1*|profile M p.1-profile M 1| * |profile M p.2-profile M 1| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by ring
  have hbound := positive_lcm_pair_bound M
    (fun d e => |profile M d-profile M 1| * |profile M e-profile M 1|) (4*C^2)
    (by positivity) (herror M)
  rw [centered_identity]
  apply (abs_add_le _ _).trans
  exact (add_le_add hmain (habs.trans hbound)).trans_eq (by dsimp [S]; ring)

end RoutePLcm

/-- The complete literal lcm sector of the native signed channels has a uniform
quadratic bound. No bound for its complementary sector is assumed. -/
theorem routeP_lcm_pair_sector_quadratic_bound :
    ∃ B : ℝ, 0≤B ∧ ∀ M : ℕ,
      |∑ p∈(Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.lcm p.1 p.2≤M),
        mobiusDivisorDilationChannel M p.1*mobiusDivisorDilationChannel M p.2| ≤
        B*(M:ℝ)^2 := by
  obtain ⟨B,hB,hbound⟩ := RoutePLcm.normalized_sector_bound
  refine ⟨B,hB,?_⟩
  intro M
  by_cases hM : M=0
  · simp [hM]
  have hm : (0:ℝ)<M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hs := Real.sqrt_pos.mpr hm
  have hs2 := Real.sq_sqrt hm.le
  have heq : (∑ p∈(Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.lcm p.1 p.2≤M),
      mobiusDivisorDilationChannel M p.1*mobiusDivisorDilationChannel M p.2) =
      (M:ℝ)*RoutePLcm.sector M (fun d e => (ArithmeticFunction.moebius d:ℝ)*
        RoutePLcm.profile M d*((ArithmeticFunction.moebius e:ℝ)*RoutePLcm.profile M e)) := by
    rw [RoutePLcm.sector,mul_sum]
    apply sum_congr rfl
    intro p _
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      mobiusDivisorDilationChannel_eq_moebius_unsigned]
    dsimp [RoutePLcm.profile]
    field_simp
    rw [hs2]
  rw [heq,abs_mul,abs_of_pos hm]
  exact (mul_le_mul_of_nonneg_left (hbound M) hm.le).trans_eq (by ring)

/-- The unpaid complementary lcm sector retains every excluded pair. -/
theorem routeP_lcm_pair_partition (M : ℕ) :
    (∑ d∈Icc 1 M,mobiusDivisorDilationChannel M d)^2 =
      (∑ p∈(Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.lcm p.1 p.2≤M),
        mobiusDivisorDilationChannel M p.1*mobiusDivisorDilationChannel M p.2)+
      (∑ p∈(Icc 1 M ×ˢ Icc 1 M).filter (fun p => M<Nat.lcm p.1 p.2),
        mobiusDivisorDilationChannel M p.1*mobiusDivisorDilationChannel M p.2) := by
  classical
  rw [pow_two,sum_mul_sum]
  simpa only [not_le,sum_product] using
    (sum_filter_add_sum_filter_not (Icc 1 M ×ˢ Icc 1 M)
      (fun p => Nat.lcm p.1 p.2≤M)
      (fun p => mobiusDivisorDilationChannel M p.1*mobiusDivisorDilationChannel M p.2)).symm

end RHTower
