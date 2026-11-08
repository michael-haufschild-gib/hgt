import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimeComponentRigidity

/-!
# Arithmetic vertex dynamics on the prime complex

Positive affine prime weights normalize barycentric coordinates within their
original face. They give a cutoff-compatible homotopy from identity to a map
whose fixed points are exactly the arithmetic prime vertices. Distinct weights
separate fixed vertices without using the Mertens count or a quadratic form.
-/

noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open EffectiveScalingGeometry HeightHomotopyArithmeticCounts HodgeTheoryWithoutVarieties

/-- The normalization of the positive arithmetic barycentric weights. -/
def primeVertexNormalizer {B : ℕ} (t : unitInterval) (x : stdSimplex ℝ (Fin (B+3))) : ℝ :=
  ∑ p, (1+(t:ℝ)*(p.val:ℝ))*x.val p

theorem primeVertexNormalizer_one_le {B : ℕ} (t : unitInterval)
    (x : stdSimplex ℝ (Fin (B+3))) : 1 ≤ primeVertexNormalizer t x := by
  rw [←x.property.2]
  apply sum_le_sum
  intro p _
  have h := mul_nonneg (mul_nonneg t.property.1 (Nat.cast_nonneg p.val)) (x.property.1 p)
  nlinarith only [h]

/-- Face-preserving normalization of the arithmetic weights. -/
def primeVertexSimplex {B : ℕ} (t : unitInterval) (x : stdSimplex ℝ (Fin (B+3))) :
    stdSimplex ℝ (Fin (B+3)) :=
  ⟨fun p => (1+(t:ℝ)*(p.val:ℝ))*x.val p/primeVertexNormalizer t x,
    (fun p => div_nonneg (mul_nonneg (by have ht := t.property.1; positivity) (x.property.1 p))
      (le_trans zero_le_one (primeVertexNormalizer_one_le t x))),by
    rw [←sum_div]
    exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one (primeVertexNormalizer_one_le t x)))⟩

theorem primeVertexSimplex_continuous (B : ℕ) :
    Continuous (fun z : unitInterval × stdSimplex ℝ (Fin (B+3)) => primeVertexSimplex z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro p
  have hn : Continuous (fun z : unitInterval × stdSimplex ℝ (Fin (B+3)) =>
      (1+(z.1:ℝ)*(p.val:ℝ))*z.2.val p) := by
    exact (continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).mul
      ((continuous_apply p).comp (continuous_subtype_val.comp continuous_snd))
  have hd : Continuous (fun z : unitInterval × stdSimplex ℝ (Fin (B+3)) =>
      primeVertexNormalizer z.1 z.2) := by
    unfold primeVertexNormalizer
    apply continuous_finsetSum
    intro q _
    exact (continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).mul
      ((continuous_apply q).comp (continuous_subtype_val.comp continuous_snd))
  exact hn.div hd (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (primeVertexNormalizer_one_le z.1 z.2)))

theorem primeVertexSimplex_support {B : ℕ} (t : unitInterval)
    (x : stdSimplex ℝ (Fin (B+3))) (S : Finset (Fin (B+3))) (hx : x∈supportFace S) :
    primeVertexSimplex t x∈supportFace S := by
  intro p hp
  change (1+(t:ℝ)*(p.val:ℝ))*x.val p/primeVertexNormalizer t x=0
  have hz : x.val p=0 := hx p hp
  rw [hz,mul_zero,zero_div]

theorem primeVertexSimplex_zero {B : ℕ} (x : stdSimplex ℝ (Fin (B+3))) :
    primeVertexSimplex 0 x=x := by
  have hd : primeVertexNormalizer 0 x=1 := by
    simp only [primeVertexNormalizer,show ((0:unitInterval):ℝ)=0 from rfl,zero_mul,add_zero,one_mul,x.property.2]
  apply Subtype.ext
  funext p
  change (1+(0:unitInterval).val*(p.val:ℝ))*x.val p/primeVertexNormalizer 0 x=x.val p
  rw [hd]
  simp only [show ((0:unitInterval):ℝ)=0 from rfl,zero_mul,add_zero,one_mul,div_one]

/-- Arithmetic normalization restricted to the original prime faces. -/
def primeVertexMotion (B N : ℕ) : C(unitInterval × PrimeHeightSpace B N,PrimeHeightSpace B N) where
  toFun z := ⟨primeVertexSimplex z.1 z.2.val,by
    obtain ⟨S,hS,hx⟩ := mem_faceFamilySpace.mp z.2.property
    exact mem_faceFamilySpace.mpr ⟨S,hS,primeVertexSimplex_support z.1 z.2.val S hx⟩⟩
  continuous_toFun := ((primeVertexSimplex_continuous B).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The arithmetic self-map multiplies vertex coordinates by their label plus one. -/
def primeVertexMap (B N : ℕ) : C(PrimeHeightSpace B N,PrimeHeightSpace B N) :=
  (primeVertexMotion B N).comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩

/-- The map is explicitly homotopic to identity within every original arithmetic face. -/
def primeVertexMapHomotopy (B N : ℕ) : (ContinuousMap.id _).Homotopy (primeVertexMap B N) where
  toContinuousMap := primeVertexMotion B N
  map_zero_left x := Subtype.ext (primeVertexSimplex_zero x.val)
  map_one_left _ := rfl

/-- Increasing the conductor cutoff leaves the arithmetic dynamics unchanged. -/
theorem primeVertexMap_natural (B : ℕ) {N M : ℕ} (h : N ≤ M) (x : PrimeHeightSpace B N) :
    heightInclusion B h (primeVertexMap B N x)=primeVertexMap B M (heightInclusion B h x) := rfl

/-- Every simplex vertex is fixed throughout arithmetic normalization. -/
theorem primeVertexSimplex_vertex {B : ℕ} (t : unitInterval) (p : Fin (B+3)) :
    primeVertexSimplex t (stdSimplex.vertex (S := ℝ) p)=stdSimplex.vertex (S := ℝ) p := by
  have hd : primeVertexNormalizer t (stdSimplex.vertex (S := ℝ) p)=1+(t:ℝ)*(p.val:ℝ) := by
    unfold primeVertexNormalizer
    change ∑ q, (1+(t:ℝ)*(q.val:ℝ))*((Pi.single p (1:ℝ) : Fin (B+3) → ℝ) q)=_
    simp only [Pi.single_apply]
    rw [sum_eq_single p]
    · simp only [ite_true,mul_one]
    · intro q _ hq
      rw [if_neg hq,mul_zero]
    · exact fun h => (h (mem_univ p)).elim
  have hp : 0 < 1+(t:ℝ)*(p.val:ℝ) := by
    have ht := t.property.1
    positivity
  apply Subtype.ext
  funext q
  change (1+(t:ℝ)*(q.val:ℝ))*(stdSimplex.vertex (S := ℝ) p).val q/
    primeVertexNormalizer t (stdSimplex.vertex (S := ℝ) p)=(stdSimplex.vertex (S := ℝ) p).val q
  rw [hd]
  change (1+(t:ℝ)*(q.val:ℝ))*((Pi.single p (1:ℝ) : Fin (B+3) → ℝ) q)/(1+(t:ℝ)*(p.val:ℝ))=(Pi.single p (1:ℝ) : Fin (B+3) → ℝ) q
  simp only [Pi.single_apply]
  by_cases hq : q=p
  · subst q
    rw [if_pos rfl,mul_one,div_self hp.ne']
  · rw [if_neg hq,mul_zero,zero_div]

/-- Distinct arithmetic weights allow no fixed point with more than one nonzero coordinate. -/
theorem primeVertexSimplex_fixed_iff {B : ℕ} (x : stdSimplex ℝ (Fin (B+3))) :
    primeVertexSimplex 1 x=x ↔ ∃ p,x=stdSimplex.vertex (S := ℝ) p := by
  constructor
  · intro hx
    have hex : ∃ p,x.val p≠0 := by
      by_contra h
      push Not at h
      have hs := x.property.2
      simp only [h,sum_const_zero] at hs
      exact zero_ne_one hs
    obtain ⟨p,hp⟩ := hex
    have hd := ne_of_gt (lt_of_lt_of_le zero_lt_one (primeVertexNormalizer_one_le 1 x))
    have hw (q : Fin (B+3)) (hq : x.val q≠0) : 1+(q.val:ℝ)=primeVertexNormalizer 1 x := by
      have he := congrArg (fun y : stdSimplex ℝ (Fin (B+3)) => y.val q) hx
      change (1+(1:unitInterval).val*(q.val:ℝ))*x.val q/primeVertexNormalizer 1 x=x.val q at he
      simp only [show ((1:unitInterval):ℝ)=1 from rfl,one_mul] at he
      have hh := (div_eq_iff hd).mp he
      rw [mul_comm (x.val q)] at hh
      exact mul_right_cancel₀ hq hh
    have hz (q : Fin (B+3)) (hqp : q≠p) : x.val q=0 := by
      by_contra hq
      have he : (q.val:ℝ)=(p.val:ℝ) := by linarith only [hw q hq,hw p hp]
      exact hqp (Fin.ext (by exact_mod_cast he))
    have hsum : ∑ q,x.val q=x.val p := sum_eq_single p (fun q _ hq => hz q hq)
      (fun h => (h (mem_univ p)).elim)
    have hp1 : x.val p=1 := hsum.symm.trans x.property.2
    refine ⟨p,Subtype.ext ?_⟩
    funext q
    change x.val q=(Pi.single p (1:ℝ) : Fin (B+3) → ℝ) q
    by_cases hq : q=p
    · subst q
      simpa only [Pi.single_eq_same] using hp1
    · rw [Pi.single_eq_of_ne hq,hz q hq]
  · rintro ⟨p,rfl⟩
    exact primeVertexSimplex_vertex 1 p

/-- The complete fixed-point set consists exactly of the original prime vertices. -/
theorem primeVertexMap_fixed_iff (B N : ℕ) (x : PrimeHeightSpace B N) :
    primeVertexMap B N x=x ↔
      ∃ (p : Fin (B+3)) (hp : p.val.Prime) (hpN : p.val≤N),x=primeVertex p hp hpN := by
  constructor
  · intro hx
    have he : primeVertexSimplex 1 x.val=x.val := congrArg Subtype.val hx
    obtain ⟨p,hp⟩ := (primeVertexSimplex_fixed_iff x.val).mp he
    obtain ⟨S,hS,hxS⟩ := mem_faceFamilySpace.mp x.property
    have hpS : p∈S := by
      by_contra hn
      have hz := hxS p hn
      rw [hp] at hz
      change (Pi.single p (1:ℝ) : Fin (B+3) → ℝ) p=0 at hz
      exact one_ne_zero (by simpa only [Pi.single_eq_same] using hz)
    have hs := mem_primeHeightFaces.mp hS
    have hpN : p.val≤N := (Nat.le_of_dvd (prod_pos (fun q hq => (hs.1 q hq).pos))
      (dvd_prod_of_mem (fun q : Fin (B+3) => q.val) hpS)).trans hs.2
    exact ⟨p,hs.1 p hpS,hpN,Subtype.ext hp⟩
  · rintro ⟨p,hp,hpN,rfl⟩
    exact Subtype.ext (primeVertexSimplex_vertex 1 p)

#print axioms primeVertexSimplex_continuous
#print axioms primeVertexMapHomotopy
#print axioms primeVertexMap_natural
#print axioms primeVertexSimplex_vertex
#print axioms primeVertexSimplex_fixed_iff
#print axioms primeVertexMap_fixed_iff
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
