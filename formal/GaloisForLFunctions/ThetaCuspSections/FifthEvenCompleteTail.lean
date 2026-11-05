import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingTailReserve
import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenOtherTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPureTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenIntegratedRemainder
/-!
# Complete fifth even theta tails

The leading theta pairs release two gamma corrections. The first pays
pair `(1,3)`; the cubic correction pays the four other unequal pairs and
the infinite remainder. Positive pure-atom tails complete the exact
native density. Exponential substitution gives strict tail positivity
at every nonnegative logarithmic cutoff.
-/
noncomputable section
open MeasureTheory Set Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthCompleteTail
open _root_.RHTower FifthAtomTail FifthRateTail FifthRemainder FifthTailRemainder
open FourAtomCauchyTail _root_.RHTower.ThetaCuspOddFourThreeAtom
open _root_.HTGeometry.SignedPoisson

private theorem radialCenter_scale {t : ℝ} (ht : 0<t) :
 thetaCuspSingleAtomReflectionScale 1 (radialCenter t)=t := by
 unfold radialCenter thetaCuspSingleAtomReflectionScale
 rw [show 2*(Real.log (t/Real.pi)/2)=Real.log (t/Real.pi) by ring,
  Real.exp_log (div_pos ht Real.pi_pos)]
 norm_num
 field_simp

private theorem sourceUnit_scaled (x : ℝ) :
 (Real.pi^(1/2:ℝ)/4)*sourceUnit x/thetaCuspSingleAtomReflectionScale 1 x=
  boundary (thetaCuspSingleAtomReflectionScale 1 x) := by
 have hq : 0<thetaCuspSingleAtomReflectionScale 1 x := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity
 have hscale : thetaCuspSingleAtomReflectionScale 1 x=Real.pi*Real.exp (2*x) := by
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
 have hp : (thetaCuspSingleAtomReflectionScale 1 x)^(3/2:ℝ)=
   thetaCuspSingleAtomReflectionScale 1 x*Real.pi^(1/2:ℝ)*Real.exp x := by
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hq,Real.rpow_one,hscale,
   Real.mul_rpow Real.pi_pos.le (Real.exp_pos _).le,← Real.exp_mul,
   show (2*x)*(1/2)=x by ring]
  ring
 have he : Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)=
   Real.exp x*Real.exp (-2*thetaCuspSingleAtomReflectionScale 1 x) := by
  rw [← Real.exp_add]
  congr 1
  ring
 unfold sourceUnit boundary
 rw [hp,he]
 field_simp [hq.ne']

/-- Signed radial density of one ordered theta-atom pair. -/
def pairDensity (a b k : ℕ) (t : ℝ) : ℝ :=
 ((a:ℝ)^2*(b:ℝ)^2)*rateBoundary ((a:ℝ)^2+(b:ℝ)^2) t*
  (thetaPairRadialEvenPolynomial ((a:ℝ)^2*(b:ℝ)^2*t^2) k).eval
   (((a:ℝ)^2+(b:ℝ)^2)*t)

/-- The reflected source normalization preserves every ordered pair exactly. -/
theorem pairDensity_eq (a b k : ℕ) {t : ℝ} (ht : 0<t) :
 (Real.pi^(1/2:ℝ)/4)*((-1:ℝ)^k*
  thetaCuspAtomPairReflectionJet (2*k) a b (radialCenter t))/t=
  pairDensity a b k t := by
 have hscale := radialCenter_scale ht
 have hpair : (-1:ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b (radialCenter t)=
   sourceUnit (radialCenter t)*
    (((a:ℝ)^2*(b:ℝ)^2)*Real.exp (-(((a:ℝ)^2+(b:ℝ)^2)-2)*t)*
     (thetaPairRadialEvenPolynomial ((a:ℝ)^2*(b:ℝ)^2*t^2) k).eval
      (((a:ℝ)^2+(b:ℝ)^2)*t)) := by
  rw [signed_pair_even,hscale]
  have he : Real.exp (radialCenter t-((a:ℝ)^2+(b:ℝ)^2)*t)=
    Real.exp (radialCenter t-2*t)*Real.exp (-(((a:ℝ)^2+(b:ℝ)^2)-2)*t) := by
   rw [← Real.exp_add]
   congr 1
   ring
  rw [he]
  unfold sourceUnit
  rw [hscale]
  ring
 have hunit := sourceUnit_scaled (radialCenter t)
 rw [hscale] at hunit
 rw [hpair]
 calc
  _ = ((Real.pi^(1/2:ℝ)/4)*sourceUnit (radialCenter t)/t)*
    (((a:ℝ)^2*(b:ℝ)^2)*Real.exp (-(((a:ℝ)^2+(b:ℝ)^2)-2)*t)*
     (thetaPairRadialEvenPolynomial ((a:ℝ)^2*(b:ℝ)^2*t^2) k).eval
      (((a:ℝ)^2+(b:ℝ)^2)*t)) := by ring
  _ = _ := by rw [hunit]; unfold pairDensity; rw [rateBoundary_relative]; ring

/-- The retained reflected source contains precisely the sixteen radial pair densities. -/
theorem fourDensity_eq_sum (k : ℕ) {t : ℝ} (ht : 0<t) :
 (Real.pi^(1/2:ℝ)/4)*((-1:ℝ)^k*
  thetaCuspFourAtomReflectionJet (2*k) (radialCenter t))/t=
  ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4, pairDensity (a+1) (b+1) k t := by
 rw [fourAtomJet_eq_sum]
 simp only [Finset.mul_sum,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro a ha
 apply Finset.sum_congr rfl
 intro b hb
 exact pairDensity_eq (a+1) (b+1) k ht

private theorem pairDensity_symm (a b k : ℕ) (t : ℝ) :
 pairDensity a b k t=pairDensity b a k t := by
 simp only [pairDensity,mul_comm ((a:ℝ)^2) ((b:ℝ)^2),
  add_comm ((a:ℝ)^2) ((b:ℝ)^2)]

/-- The sixteen ordered pairs are four pure terms and six doubled unequal terms. -/
theorem fourDensity_eq_grouped (k : ℕ) {t : ℝ} (ht : 0<t) :
 (Real.pi^(1/2:ℝ)/4)*((-1:ℝ)^k*
  thetaCuspFourAtomReflectionJet (2*k) (radialCenter t))/t=
 pairDensity 1 1 k t+2*pairDensity 1 2 k t+2*pairDensity 1 3 k t+
  2*pairDensity 1 4 k t+pairDensity 2 2 k t+2*pairDensity 2 3 k t+
  2*pairDensity 2 4 k t+pairDensity 3 3 k t+2*pairDensity 3 4 k t+
  pairDensity 4 4 k t := by
 rw [fourDensity_eq_sum k ht]
 simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,zero_add]
 rw [pairDensity_symm 2 1 k t,pairDensity_symm 3 1 k t,
  pairDensity_symm 4 1 k t,pairDensity_symm 3 2 k t,
  pairDensity_symm 4 2 k t,pairDensity_symm 4 3 k t]
 ring

/-- Literal native signed density after the exponential radial substitution. -/
def nativeDensity (k : ℕ) (t : ℝ) : ℝ :=
 (Real.pi^(1/2:ℝ)/4)*((-1:ℝ)^k*
  thetaCuspNativeReflectionJet (2*k) (radialCenter t))/t

/-- All ordered retained pairs and the literal omitted remainder recover the native source. -/
theorem nativeDensity_eq_pairs_add_error (k : ℕ) {t : ℝ} (ht : 0<t) :
 nativeDensity k t=
  (∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4, pairDensity (a+1) (b+1) k t)+
  radialError k t := by
 rw [← fourDensity_eq_sum k ht]
 unfold nativeDensity radialError
 ring

/-- Four pure pairs, six doubled unequal pairs, and the omitted source recover the native density. -/
theorem nativeDensity_eq_grouped_add_error (k : ℕ) {t : ℝ} (ht : 0<t) :
 nativeDensity k t=
 (pairDensity 1 1 k t+2*pairDensity 1 2 k t+2*pairDensity 1 3 k t+
  2*pairDensity 1 4 k t+pairDensity 2 2 k t+2*pairDensity 2 3 k t+
  2*pairDensity 2 4 k t+pairDensity 3 3 k t+2*pairDensity 3 4 k t+
  pairDensity 4 4 k t)+radialError k t := by
 rw [nativeDensity_eq_pairs_add_error k ht,← fourDensity_eq_sum k ht,
  fourDensity_eq_grouped k ht]

private theorem radialCenter_inverse (s : ℝ) :
 radialCenter (Real.pi*Real.exp s)=s/2 := by
 unfold radialCenter
 rw [show Real.pi*Real.exp s/Real.pi=Real.exp s by field_simp [Real.pi_ne_zero],Real.log_exp]

private theorem native_source_scaled (s : ℝ) (k : ℕ) :
 (Real.pi^(1/2:ℝ)/4)*thetaCuspNativeSignedJet (s/2) (2*k)=
 (Real.pi*Real.exp s)*nativeDensity k (Real.pi*Real.exp s) := by
 rw [_root_.RHTower.ThetaCuspOddFourNativeBulk.signedJet_even_eq,
   nativeDensity,radialCenter_inverse]
 field_simp [(mul_pos Real.pi_pos (Real.exp_pos s)).ne']

/-- The complete fifth even tail in radial coordinates. -/
def radialNativeTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 ∫ t in Ioi q, nativeDensity (i.val+j.val) t

/-- The literal fifth even native signed-jet tail. -/
def nativeTailMatrix (r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 ∫ s in Ioi r, thetaCuspNativeSignedJet (s/2) (2*(i.val+j.val))

/-- Exponential scale change preserves every literal native tail entry. -/
theorem nativeTailMatrix_scaled (r : ℝ) :
 (Real.pi^(1/2:ℝ)/4) • nativeTailMatrix r=radialNativeTailMatrix (Real.pi*Real.exp r) := by
 ext i j
 change (Real.pi^(1/2:ℝ)/4)*
  (∫ s in Ioi r, thetaCuspNativeSignedJet (s/2) (2*(i.val+j.val)))=_
 rw [← integral_const_mul]
 rw [radialNativeTailMatrix,integral_scale]
 exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => native_source_scaled s (i.val+j.val))

open FifthAtomTail FifthRateTail

/-- All four pure atoms, twelve unequal ordered pairs, and the literal remaining source. -/
def radialTailDecomposition (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 FifthMixedTail.leadingRadialTailMatrix q+
 FifthThirdTail.thirdRadialTailMatrix q+
 FifthOtherTail.p14.pairRadialTailMatrix q+
 FifthOtherTail.p23.pairRadialTailMatrix q+
 FifthOtherTail.p24.pairRadialTailMatrix q+
 FifthOtherTail.p34.pairRadialTailMatrix q+
 FifthPureTail.pureRadialTailMatrix 4 q+
 FifthPureTail.pureRadialTailMatrix 9 q+
 FifthPureTail.pureRadialTailMatrix 16 q+
 FifthTailRemainder.errorMatrix q

/-- The exact gamma allocations cancel, leaving a strict complete radial comparison. -/
theorem radialTailDecomposition_posDef {q : ℝ} (hq : 3≤q) :
 (radialTailDecomposition q).PosDef := by
 have hL := FifthMixedTailReserve.leadingRadialTailMatrix_reserve_posDef hq
 have h13 := FifthThirdTail.thirdRadialTailMatrix_reserve_posDef hq
 have h14 := FifthOtherTail.p14.pairRadialTailMatrix_reserve_posDef hq
 have h23 := FifthOtherTail.p23.pairRadialTailMatrix_reserve_posDef hq
 have h24 := FifthOtherTail.p24.pairRadialTailMatrix_reserve_posDef hq
 have h34 := FifthOtherTail.p34.pairRadialTailMatrix_reserve_posDef hq
 have h2 := FifthPureTail.pureRadialTailMatrix_posDef (by norm_num : (1:ℝ)≤4) hq
 have h3 := FifthPureTail.pureRadialTailMatrix_posDef (by norm_num : (1:ℝ)≤9) hq
 have h4 := FifthPureTail.pureRadialTailMatrix_posDef (by norm_num : (1:ℝ)≤16) hq
 have hR := FifthTailRemainder.errorMatrix_add_reserve_posSemidef hq
 have hF13 := hL.add_posSemidef h13.posSemidef
 have hF14 := hF13.add_posSemidef h14.posSemidef
 have hF23 := hF14.add_posSemidef h23.posSemidef
 have hF24 := hF23.add_posSemidef h24.posSemidef
 have hFinite := hF24.add_posSemidef h34.posSemidef
 have hP2 := hFinite.add_posSemidef h2.posSemidef
 have hP3 := hP2.add_posSemidef h3.posSemidef
 have hP4 := hP3.add_posSemidef h4.posSemidef
 have hSum := hP4.add_posSemidef hR
 convert hSum using 1
 ext i j
 simp only [radialTailDecomposition,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
 ring

open FifthMixedTail

private theorem mixedLinear_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 mixedLinear (fun n => q^n) k=
  (_root_.RHTower.thetaPairRadialEvenPolynomial (4*q^2) k).eval (5*q) := by
 rw [EightCrossData.mixed_eq q k hk]
 interval_cases k <;> simp only [mixedLinear,EightCrossData.bMoment,pow_zero,pow_one,mul_one]
 all_goals rfl

private theorem mixedLinear_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 mixedLinear m k=∑ j ∈ Finset.range 19,
  mixedLinear (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [mixedLinear,Finset.sum_range_succ] <;> ring

private theorem mixed_density_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t => rateBoundary 5 t*
  (thetaPairRadialEvenPolynomial (4*t^2) k).eval (5*t)) (Ioi q) := by
 have he : (fun t => rateBoundary 5 t*
  (thetaPairRadialEvenPolynomial (4*t^2) k).eval (5*t))=
  fun t => ∑ j ∈ Finset.range 19,
   mixedLinear (fun n => if n=j then 1 else 0) k*(rateBoundary 5 t*t^j) := by
  funext t
  rw [← mixedLinear_pow t k hk,← mixedLinear_smul _ _ k hk,mixedLinear_sum k hk]
 rw [he]
 exact integrable_finsetSum _ (fun j _ =>
  (weighted_power_integrable (by norm_num : (0:ℝ)<5) j hq).const_mul _)

private theorem pure_pairDensity_eq (n k : ℕ) (t : ℝ) :
 pairDensity n n k t=((n:ℝ)^2)^2*FifthPureTail.pureDensity ((n:ℝ)^2) k t := by
 have hs : (n:ℝ)^2+(n:ℝ)^2=2*(n:ℝ)^2 := by ring
 have hp : (n:ℝ)^2*(n:ℝ)^2=((n:ℝ)^2)^2 := by ring
 have ha : ((n:ℝ)^2)^2*t^2=((n:ℝ)^2*t)^2 := by ring
 have he : (2*(n:ℝ)^2)*t=2*((n:ℝ)^2*t) := by ring
 simp only [pairDensity,FifthPureTail.pureDensity,hs,hp,ha,he]
 ring

private theorem pure_pair_integrable (n : ℕ) (hn : 0<n) (k : ℕ) (hk : k≤8)
 {q : ℝ} (hq : 0<q) : IntegrableOn (pairDensity n n k) (Ioi q) := by
 have hnR : (0:ℝ)<(n:ℝ) := by exact_mod_cast hn
 have hi := (FifthPureTail.pureDensity_integrable
  (by positivity : (0:ℝ)<(n:ℝ)^2) hq k hk).const_mul (((n:ℝ)^2)^2)
 exact IntegrableOn.congr_fun hi (fun t _ => (pure_pairDensity_eq n k t).symm) measurableSet_Ioi

private theorem pairIntegral_eq (a b k : ℕ) (q : ℝ) :
 (∫ t in Ioi q, pairDensity a b k t)=((a:ℝ)^2*(b:ℝ)^2)*
  ∫ t in Ioi q, rateBoundary ((a:ℝ)^2+(b:ℝ)^2) t*
   (thetaPairRadialEvenPolynomial ((a:ℝ)^2*(b:ℝ)^2*t^2) k).eval
    (((a:ℝ)^2+(b:ℝ)^2)*t) := by
 rw [← integral_const_mul]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro t ht
 dsimp only [pairDensity]
 ring

private theorem integral_pure_pair_eq (n : ℕ) (q : ℝ) (i j : Fin 5) :
 (∫ t in Ioi q, pairDensity n n (i.val+j.val) t)=
  FifthPureTail.pureRadialTailMatrix ((n:ℝ)^2) q i j := by
 rw [show (fun t => pairDensity n n (i.val+j.val) t)=
  (fun t => ((n:ℝ)^2)^2*FifthPureTail.pureDensity ((n:ℝ)^2) (i.val+j.val) t) from
  funext (fun t => pure_pairDensity_eq n (i.val+j.val) t),integral_const_mul]
 rfl

private theorem integral_first_pair_eq (q : ℝ) (i j : Fin 5) :
 (∫ t in Ioi q, pairDensity 1 1 (i.val+j.val) t)=FifthAtomTail.radialTailMatrix q i j := by
 rw [pairIntegral_eq]
 norm_num only [FifthAtomTail.radialTailMatrix,rateBoundary,boundary,one_mul,mul_one]

private theorem pair12_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (pairDensity 1 2 k) (Ioi q) := by
 have hi := (mixed_density_integrable k hk hq).const_mul (4:ℝ)
 exact IntegrableOn.congr_fun hi (fun t _ => by norm_num only [pairDensity,one_mul,mul_one]; ring) measurableSet_Ioi

private theorem integral_pair12_eq (q : ℝ) (i j : Fin 5) :
 2*(∫ t in Ioi q, pairDensity 1 2 (i.val+j.val) t)=FifthMixedTail.mixedRadialTailMatrix q i j := by
 rw [pairIntegral_eq]
 norm_num only [FifthMixedTail.mixedRadialTailMatrix,FifthMixedTail.fiveBoundary,rateBoundary,one_mul,mul_one]; ring

private theorem pair13_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (pairDensity 1 3 k) (Ioi q) := by
 have hi := (FifthThirdTail.third_radial_integrable k hk hq).const_mul (9:ℝ)
 exact IntegrableOn.congr_fun hi (fun t _ => by norm_num only [pairDensity,one_mul,mul_one]; ring) measurableSet_Ioi

private theorem integral_pair13_eq (q : ℝ) (i j : Fin 5) :
 2*(∫ t in Ioi q, pairDensity 1 3 (i.val+j.val) t)=FifthThirdTail.thirdRadialTailMatrix q i j := by
 rw [pairIntegral_eq]
 norm_num only [FifthThirdTail.thirdRadialTailMatrix,one_mul,mul_one]; ring

private theorem pair14_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (pairDensity 1 4 k) (Ioi q) := by
 have hi := (FifthOtherTail.p14.pair_radial_integrable k hk hq).const_mul (16:ℝ)
 exact IntegrableOn.congr_fun hi (fun t _ => by norm_num only [pairDensity,one_mul,mul_one]; ring) measurableSet_Ioi

private theorem integral_pair14_eq (q : ℝ) (i j : Fin 5) :
 2*(∫ t in Ioi q, pairDensity 1 4 (i.val+j.val) t)=FifthOtherTail.p14.pairRadialTailMatrix q i j := by
 rw [pairIntegral_eq]
 norm_num only [FifthOtherTail.p14.pairRadialTailMatrix,one_mul,mul_one]; ring

private theorem pair23_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (pairDensity 2 3 k) (Ioi q) := by
 have hi := (FifthOtherTail.p23.pair_radial_integrable k hk hq).const_mul (36:ℝ)
 exact IntegrableOn.congr_fun hi (fun t _ => by norm_num only [pairDensity,one_mul,mul_one]; ring) measurableSet_Ioi

private theorem integral_pair23_eq (q : ℝ) (i j : Fin 5) :
 2*(∫ t in Ioi q, pairDensity 2 3 (i.val+j.val) t)=FifthOtherTail.p23.pairRadialTailMatrix q i j := by
 rw [pairIntegral_eq]
 norm_num only [FifthOtherTail.p23.pairRadialTailMatrix,one_mul,mul_one]; ring

private theorem pair24_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (pairDensity 2 4 k) (Ioi q) := by
 have hi := (FifthOtherTail.p24.pair_radial_integrable k hk hq).const_mul (64:ℝ)
 exact IntegrableOn.congr_fun hi (fun t _ => by norm_num only [pairDensity,one_mul,mul_one]; ring) measurableSet_Ioi

private theorem integral_pair24_eq (q : ℝ) (i j : Fin 5) :
 2*(∫ t in Ioi q, pairDensity 2 4 (i.val+j.val) t)=FifthOtherTail.p24.pairRadialTailMatrix q i j := by
 rw [pairIntegral_eq]
 norm_num only [FifthOtherTail.p24.pairRadialTailMatrix,one_mul,mul_one]; ring

private theorem pair34_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (pairDensity 3 4 k) (Ioi q) := by
 have hi := (FifthOtherTail.p34.pair_radial_integrable k hk hq).const_mul (144:ℝ)
 exact IntegrableOn.congr_fun hi (fun t _ => by norm_num only [pairDensity,one_mul,mul_one]; ring) measurableSet_Ioi

private theorem integral_pair34_eq (q : ℝ) (i j : Fin 5) :
 2*(∫ t in Ioi q, pairDensity 3 4 (i.val+j.val) t)=FifthOtherTail.p34.pairRadialTailMatrix q i j := by
 rw [pairIntegral_eq]
 norm_num only [FifthOtherTail.p34.pairRadialTailMatrix,one_mul,mul_one]; ring

/-- Every entry of the retained decomposition is the complete literal radial integral. -/
theorem radialNativeTailMatrix_eq_decomposition {q : ℝ} (hq : 3≤q) :
 radialNativeTailMatrix q=radialTailDecomposition q := by
 have hq0 : 0<q := by linarith only [hq]
 ext i j
 have hk : i.val+j.val≤8 := by omega
 have h11 := pure_pair_integrable 1 (by norm_num) (i.val+j.val) hk hq0
 have h12 := (pair12_integrable (i.val+j.val) hk hq0).const_mul (2:ℝ)
 have h13 := (pair13_integrable (i.val+j.val) hk hq0).const_mul (2:ℝ)
 have h14 := (pair14_integrable (i.val+j.val) hk hq0).const_mul (2:ℝ)
 have h22 := pure_pair_integrable 2 (by norm_num) (i.val+j.val) hk hq0
 have h23 := (pair23_integrable (i.val+j.val) hk hq0).const_mul (2:ℝ)
 have h24 := (pair24_integrable (i.val+j.val) hk hq0).const_mul (2:ℝ)
 have h33 := pure_pair_integrable 3 (by norm_num) (i.val+j.val) hk hq0
 have h34 := (pair34_integrable (i.val+j.val) hk hq0).const_mul (2:ℝ)
 have h44 := pure_pair_integrable 4 (by norm_num) (i.val+j.val) hk hq0
 have h2 := h11.add h12
 have h3 := h2.add h13
 have h4 := h3.add h14
 have h5 := h4.add h22
 have h6 := h5.add h23
 have h7 := h6.add h24
 have h8 := h7.add h33
 have h9 := h8.add h34
 have h10 := h9.add h44
 have hE := FifthTailRemainder.radialError_integrable (i.val+j.val) hq
 have e10 := integral_add h10 hE
 have e9 := integral_add h9 h44
 have e8 := integral_add h8 h34
 have e7 := integral_add h7 h33
 have e6 := integral_add h6 h24
 have e5 := integral_add h5 h23
 have e4 := integral_add h4 h22
 have e3 := integral_add h3 h14
 have e2 := integral_add h2 h13
 have e1 := integral_add h11 h12
 dsimp only [Pi.add_apply] at e10 e9 e8 e7 e6 e5 e4 e3 e2 e1
 change (∫ t in Ioi q, nativeDensity (i.val+j.val) t)=
  FifthAtomTail.radialTailMatrix q i j+FifthMixedTail.mixedRadialTailMatrix q i j+
  FifthThirdTail.thirdRadialTailMatrix q i j+FifthOtherTail.p14.pairRadialTailMatrix q i j+
  FifthOtherTail.p23.pairRadialTailMatrix q i j+FifthOtherTail.p24.pairRadialTailMatrix q i j+
  FifthOtherTail.p34.pairRadialTailMatrix q i j+FifthPureTail.pureRadialTailMatrix 4 q i j+
  FifthPureTail.pureRadialTailMatrix 9 q i j+FifthPureTail.pureRadialTailMatrix 16 q i j+
  ∫ t in Ioi q, radialError (i.val+j.val) t
 rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
  nativeDensity_eq_grouped_add_error (i.val+j.val) (hq0.trans ht)),
  e10,e9,e8,e7,e6,e5,e4,e3,e2,e1]
 simp only [integral_const_mul]
 rw [integral_first_pair_eq,integral_pair12_eq,integral_pair13_eq,
  integral_pair14_eq,integral_pair23_eq,integral_pair24_eq,integral_pair34_eq,
  integral_pure_pair_eq 2,integral_pure_pair_eq 3,integral_pure_pair_eq 4]
 norm_num only
 ring

/-- The complete fifth even radial tail is strict from scale three. -/
theorem radialNativeTailMatrix_posDef {q : ℝ} (hq : 3≤q) :
 (radialNativeTailMatrix q).PosDef := by
 rw [radialNativeTailMatrix_eq_decomposition hq]
 exact radialTailDecomposition_posDef hq

/-- Every nonnegative cutoff has a strictly positive complete fifth even native tail. -/
theorem nativeTailMatrix_posDef {r : ℝ} (hr : 0≤r) : (nativeTailMatrix r).PosDef := by
 have he : 1≤Real.exp r := by linarith only [Real.add_one_le_exp r,hr]
 have hπ := mul_le_mul_of_nonneg_left he Real.pi_pos.le
 rw [mul_one] at hπ
 have hq : 3≤Real.pi*Real.exp r := Real.pi_gt_three.le.trans hπ
 have hp := radialNativeTailMatrix_posDef hq
 rw [← nativeTailMatrix_scaled] at hp
 have hc : 0<Real.pi^(1/2:ℝ)/4 := by positivity
 have hi := hp.smul (inv_pos.mpr hc)
 simpa only [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] using hi

end GaloisForLFunctions.ThetaCuspSections.FifthCompleteTail
