import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimeComponentRigidity
import GaloisForLFunctions.EffectiveScalingGeometry.PrimePersistenceIntervals

/-!
# Projective coordinates at arithmetic prime vertices

The open star of a prime vertex is homeomorphic to its nonnegative link cone.
The coordinates are actual barycentric ratios, so diagonal dynamics in the
cone is dynamics on the original prime complex.
-/
noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open EffectiveScalingGeometry HeightHomotopyArithmeticCounts HodgeTheoryWithoutVarieties

/-- Nonnegative link cone at a vertex of the actual prime-product complex. -/
def primeVertexCone (B N : ℕ) (p : Fin (B+3)) : Set (Fin (B+3) → ℝ) :=
  {y | (∀ q, 0≤y q) ∧ y p=0 ∧
    ∃ S∈primeHeightFaces B N, p∈S ∧ ∀ q∉S,y q=0}

/-- The barycentric open star, with no enlargement of the prime-product cutoff. -/
def primeVertexOpenStar (B N : ℕ) (p : Fin (B+3)) : Set (PrimeHeightSpace B N) :=
  {x | 0<x.val.val p}

def primeConeDenominator {B N : ℕ} {p : Fin (B+3)} (y : primeVertexCone B N p) : ℝ :=
  1+∑ q,y.val q

theorem primeConeDenominator_pos {B N : ℕ} {p : Fin (B+3)} (y : primeVertexCone B N p) :
    0<primeConeDenominator y := by
  have hs : 0≤∑ q,y.val q := sum_nonneg (fun q _ => y.property.1 q)
  unfold primeConeDenominator
  linarith only [hs]

/-- Insert the apex coefficient one and normalize the cone coordinates. -/
def primeConeSimplex {B N : ℕ} {p : Fin (B+3)} (y : primeVertexCone B N p) :
    stdSimplex ℝ (Fin (B+3)) :=
  ⟨fun q => ((if q=p then 1 else 0)+y.val q)/primeConeDenominator y,by
    constructor
    · intro q
      exact div_nonneg (add_nonneg (by split_ifs <;> norm_num) (y.property.1 q))
        (primeConeDenominator_pos y).le
    · rw [←sum_div,sum_add_distrib]
      simp only [sum_ite_eq',mem_univ,ite_true]
      exact div_self (primeConeDenominator_pos y).ne'⟩

theorem primeConeSimplex_mem {B N : ℕ} {p : Fin (B+3)} (y : primeVertexCone B N p) :
    primeConeSimplex y∈PrimeHeightSpace B N := by
  obtain ⟨S,hS,hpS,hy⟩ := y.property.2.2
  refine mem_faceFamilySpace.mpr ⟨S,hS,?_⟩
  intro q hq
  change ((if q=p then (1:ℝ) else 0)+y.val q)/primeConeDenominator y=0
  have hqp : q≠p := fun h => hq (h ▸ hpS)
  rw [if_neg hqp,hy q hq,add_zero,zero_div]

theorem primeConeSimplex_apex {B N : ℕ} {p : Fin (B+3)} (y : primeVertexCone B N p) :
    (primeConeSimplex y).val p=1/primeConeDenominator y := by
  change ((if p=p then (1:ℝ) else 0)+y.val p)/primeConeDenominator y=_
  rw [if_pos rfl,y.property.2.1,add_zero]

def primeConeToStar {B N : ℕ} {p : Fin (B+3)} (y : primeVertexCone B N p) :
    primeVertexOpenStar B N p :=
  ⟨⟨primeConeSimplex y,primeConeSimplex_mem y⟩,by
    change 0<(primeConeSimplex y).val p
    rw [primeConeSimplex_apex]
    exact div_pos zero_lt_one (primeConeDenominator_pos y)⟩

def primeStarToCone {B N : ℕ} {p : Fin (B+3)} (x : primeVertexOpenStar B N p) :
    primeVertexCone B N p :=
  ⟨fun q => x.val.val.val q/x.val.val.val p-(if q=p then 1 else 0),by
    constructor
    · intro q
      dsimp only
      by_cases hq : q=p
      · subst q
        rw [if_pos rfl,div_self (ne_of_gt x.property),sub_self]
      · rw [if_neg hq,sub_zero]
        exact div_nonneg (x.val.val.property.1 q) x.property.le
    constructor
    · dsimp only
      rw [if_pos rfl,div_self (ne_of_gt x.property),sub_self]
    · obtain ⟨S,hS,hxS⟩ := mem_faceFamilySpace.mp x.val.property
      have hpS : p∈S := by
        by_contra h
        exact (ne_of_gt x.property) (hxS p h)
      refine ⟨S,hS,hpS,?_⟩
      intro q hq
      have hqp : q≠p := fun h => hq (h ▸ hpS)
      have hz : x.val.val.val q=0 := hxS q hq
      dsimp only
      rw [hz,zero_div,if_neg hqp,sub_zero]⟩

theorem primeStarToCone_denominator {B N : ℕ} {p : Fin (B+3)}
    (x : primeVertexOpenStar B N p) :
    primeConeDenominator (primeStarToCone x)=1/x.val.val.val p := by
  change 1+∑ q,(x.val.val.val q/x.val.val.val p-(if q=p then (1:ℝ) else 0))=_
  rw [sum_sub_distrib,←sum_div,x.val.val.property.2]
  simp only [sum_ite_eq',mem_univ,ite_true]
  ring

theorem primeStarToCone_toStar {B N : ℕ} {p : Fin (B+3)} (y : primeVertexCone B N p) :
    primeStarToCone (primeConeToStar y)=y := by
  apply Subtype.ext
  funext q
  change ((primeConeSimplex y).val q/(primeConeSimplex y).val p-
    (if q=p then (1:ℝ) else 0))=y.val q
  rw [primeConeSimplex_apex]
  change (((if q=p then (1:ℝ) else 0)+y.val q)/primeConeDenominator y)/
    (1/primeConeDenominator y)-(if q=p then (1:ℝ) else 0)=y.val q
  field_simp [(primeConeDenominator_pos y).ne']
  ring

theorem primeConeToStar_toCone {B N : ℕ} {p : Fin (B+3)}
    (x : primeVertexOpenStar B N p) : primeConeToStar (primeStarToCone x)=x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  change ((if q=p then (1:ℝ) else 0)+(primeStarToCone x).val q)/
    primeConeDenominator (primeStarToCone x)=x.val.val.val q
  rw [primeStarToCone_denominator]
  change ((if q=p then (1:ℝ) else 0)+(x.val.val.val q/x.val.val.val p-
    (if q=p then (1:ℝ) else 0)))/(1/x.val.val.val p)=x.val.val.val q
  have hp : x.val.val.val p≠0 := ne_of_gt x.property
  field_simp [hp]
  ring

/-- The cone chart identifies a genuine open subset of the original complex. -/
def primeVertexChart (B N : ℕ) (p : Fin (B+3)) :
    primeVertexCone B N p ≃ₜ primeVertexOpenStar B N p where
  toFun := primeConeToStar
  invFun := primeStarToCone
  left_inv := primeStarToCone_toStar
  right_inv := primeConeToStar_toCone
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro q
    apply Continuous.div
    · exact continuous_const.add ((continuous_apply q).comp continuous_subtype_val)
    · exact continuous_const.add (continuous_finsetSum _ (fun r _ =>
        (continuous_apply r).comp continuous_subtype_val))
    · intro y
      exact (primeConeDenominator_pos y).ne'
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro q
    have hc (r : Fin (B+3)) : Continuous (fun x : primeVertexOpenStar B N p => x.val.val.val r) :=
      (continuous_apply r).comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val))
    exact ((hc q).div (hc p) (fun x => ne_of_gt x.property)).sub continuous_const

#print axioms primeVertexChart

/-- Strictly ordered logarithmic weights make time one multiply coordinates by `q+1`. -/
def primeVertexRate {B : ℕ} (p q : Fin (B+3)) : ℝ :=
  Real.log ((q.val:ℝ)+1)-Real.log ((p.val:ℝ)+1)

theorem primeVertexRate_self {B : ℕ} (p : Fin (B+3)) : primeVertexRate p p=0 := sub_self _

/-- The local arithmetic flow preserves precisely the original allowed supports. -/
def primeConeFlow {B N : ℕ} (p : Fin (B+3)) (t : ℝ) (y : primeVertexCone B N p) :
    primeVertexCone B N p :=
  ⟨fun q => Real.exp (t*primeVertexRate p q)*y.val q,by
    refine ⟨fun q => mul_nonneg (Real.exp_pos _).le (y.property.1 q),?_,?_⟩
    · dsimp only
      rw [y.property.2.1,mul_zero]
    · obtain ⟨S,hS,hp,hy⟩ := y.property.2.2
      exact ⟨S,hS,hp,fun q hq => by dsimp only; rw [hy q hq,mul_zero]⟩⟩

theorem primeConeFlow_zero {B N : ℕ} (p : Fin (B+3)) (y : primeVertexCone B N p) :
    primeConeFlow p 0 y=y := by
  apply Subtype.ext
  funext q
  change Real.exp (0*primeVertexRate p q)*y.val q=y.val q
  rw [zero_mul,Real.exp_zero,one_mul]

theorem primeConeFlow_add {B N : ℕ} (p : Fin (B+3)) (s t : ℝ)
    (y : primeVertexCone B N p) :
    primeConeFlow p (s+t) y=primeConeFlow p s (primeConeFlow p t y) := by
  apply Subtype.ext
  funext q
  change Real.exp ((s+t)*primeVertexRate p q)*y.val q=
    Real.exp (s*primeVertexRate p q)*(Real.exp (t*primeVertexRate p q)*y.val q)
  rw [add_mul,Real.exp_add,mul_assoc]

theorem primeConeFlow_continuous (B N : ℕ) (p : Fin (B+3)) :
    Continuous (fun z : ℝ × primeVertexCone B N p => primeConeFlow p z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  exact ((continuous_fst.mul continuous_const).rexp).mul
    ((continuous_apply q).comp (continuous_subtype_val.comp continuous_snd))

/-- Mass in expanding directions in the actual projective chart. -/
def primeUpperMass {B : ℕ} (p : Fin (B+3)) (y : Fin (B+3) → ℝ) : ℝ :=
  ∑ q∈univ.filter (p<·),y q

/-- Mass in contracting directions in the actual projective chart. -/
def primeLowerMass {B : ℕ} (p : Fin (B+3)) (y : Fin (B+3) → ℝ) : ℝ :=
  ∑ q∈univ.filter (·<p),y q

/-- A local block bounds stable and unstable mass independently. -/
def primeVertexBlock (B N : ℕ) (p : Fin (B+3)) : Set (primeVertexCone B N p) :=
  {y | primeUpperMass p y.val≤1 ∧ primeLowerMass p y.val≤1}

/-- The exit lies on the unstable boundary of the local block. -/
def primeVertexExit (B N : ℕ) (p : Fin (B+3)) : Set (primeVertexBlock B N p) :=
  {y | primeUpperMass p y.val.val=1}

/-- Contract stable coordinates while retaining every unstable coordinate. -/
def primeConeStableContraction {B N : ℕ} (p : Fin (B+3)) (t : unitInterval)
    (y : primeVertexCone B N p) : primeVertexCone B N p :=
  ⟨fun q => (if q<p then 1-(t:ℝ) else 1)*y.val q,by
    refine ⟨fun q => mul_nonneg ?_ (y.property.1 q),?_,?_⟩
    · split_ifs
      · exact sub_nonneg.mpr t.property.2
      · exact zero_le_one
    · dsimp only
      rw [y.property.2.1,mul_zero]
    · obtain ⟨S,hS,hp,hy⟩ := y.property.2.2
      exact ⟨S,hS,hp,fun q hq => by dsimp only; rw [hy q hq,mul_zero]⟩⟩

theorem primeConeStableContraction_upper {B N : ℕ} (p : Fin (B+3)) (t : unitInterval)
    (y : primeVertexCone B N p) :
    primeUpperMass p (primeConeStableContraction p t y).val=primeUpperMass p y.val := by
  apply sum_congr rfl
  intro q hq
  have hqp : ¬q<p := not_lt.mpr (le_of_lt (mem_filter.mp hq).2)
  change (if q<p then 1-(t:ℝ) else 1)*y.val q=y.val q
  rw [if_neg hqp,one_mul]

theorem primeConeStableContraction_lower {B N : ℕ} (p : Fin (B+3)) (t : unitInterval)
    (y : primeVertexCone B N p) :
    primeLowerMass p (primeConeStableContraction p t y).val=(1-(t:ℝ))*primeLowerMass p y.val := by
  unfold primeLowerMass
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  change (if q<p then 1-(t:ℝ) else 1)*y.val q=(1-(t:ℝ))*y.val q
  rw [if_pos (mem_filter.mp hq).2]

def primeBlockStableContraction {B N : ℕ} (p : Fin (B+3)) (t : unitInterval)
    (y : primeVertexBlock B N p) : primeVertexBlock B N p :=
  ⟨primeConeStableContraction p t y.val,by
    constructor
    · rw [primeConeStableContraction_upper]
      exact y.property.1
    · rw [primeConeStableContraction_lower]
      have hn : 0≤primeLowerMass p y.val.val := sum_nonneg (fun q _ => y.val.property.1 q)
      exact (mul_le_of_le_one_left hn (by linarith only [t.property.1])).trans y.property.2⟩

def primeExitStableContraction {B N : ℕ} (p : Fin (B+3)) (t : unitInterval)
    (y : primeVertexExit B N p) : primeVertexExit B N p :=
  ⟨primeBlockStableContraction p t y.val,by
    change primeUpperMass p (primeConeStableContraction p t y.val.val).val=1
    rw [primeConeStableContraction_upper]
    exact y.property⟩

theorem primeExitStableContraction_zero {B N : ℕ} (p : Fin (B+3))
    (y : primeVertexExit B N p) : primeExitStableContraction p 0 y=y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  change (if q<p then 1-((0:unitInterval):ℝ) else 1)*y.val.val.val q=y.val.val.val q
  simp only [show ((0:unitInterval):ℝ)=0 from rfl,sub_zero,ite_self,one_mul]

theorem primeExitStableContraction_one_lower {B N : ℕ} (p : Fin (B+3))
    (y : primeVertexExit B N p) :
    primeLowerMass p (primeExitStableContraction p 1 y).val.val.val=0 := by
  change primeLowerMass p (primeConeStableContraction p 1 y.val.val).val=0
  rw [primeConeStableContraction_lower]
  simp only [show ((1:unitInterval):ℝ)=1 from rfl,sub_self,zero_mul]

theorem primeExitStableContraction_continuous (B N : ℕ) (p : Fin (B+3)) :
    Continuous (fun z : unitInterval × primeVertexExit B N p => primeExitStableContraction p z.1 z.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  have hc : Continuous (fun z : unitInterval × primeVertexExit B N p => z.2.val.val.val q) :=
    (continuous_apply q).comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
  by_cases hq : q<p
  · change Continuous (fun z : unitInterval × primeVertexExit B N p =>
      (if q<p then 1-(z.1:ℝ) else 1)*z.2.val.val.val q)
    simp only [if_pos hq]
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hc
  · change Continuous (fun z : unitInterval × primeVertexExit B N p =>
      (if q<p then 1-(z.1:ℝ) else 1)*z.2.val.val.val q)
    simp only [if_neg hq,one_mul]
    exact hc

#print axioms primeConeFlow_add
#print axioms primeConeFlow_continuous
#print axioms primeExitStableContraction_continuous


/-- Arithmetic ordering agrees with expansion in the local flow. -/
theorem primeVertexRate_pos {B : ℕ} {p q : Fin (B+3)} (h : p<q) :
    0<primeVertexRate p q := by
  apply sub_pos.mpr
  apply Real.log_lt_log (by positivity)
  exact_mod_cast (show p.val+1<q.val+1 by omega)

theorem primeVertexRate_ne_zero {B : ℕ} {p q : Fin (B+3)} (h : q≠p) :
    primeVertexRate p q≠0 := by
  rcases lt_or_gt_of_ne h with hq | hq
  · have hp := primeVertexRate_pos hq
    unfold primeVertexRate at hp ⊢
    linarith only [hp]
  · exact (primeVertexRate_pos hq).ne'

/-- The two mass bounds control every nonnegative cone coordinate. -/
theorem primeVertexBlock_coordinate_le {B N : ℕ} {p : Fin (B+3)}
    (y : primeVertexCone B N p) (hy : y∈primeVertexBlock B N p) (q : Fin (B+3)) : y.val q≤1 := by
  rcases lt_trichotomy q p with hq | hq | hq
  · exact (single_le_sum (fun r _ => y.property.1 r)
      (mem_filter.mpr ⟨mem_univ q,hq⟩)).trans hy.2
  · rw [hq,y.property.2.1]
    exact zero_le_one
  · exact (single_le_sum (fun r _ => y.property.1 r)
      (mem_filter.mpr ⟨mem_univ q,hq⟩)).trans hy.1

/-- Only the apex has a complete orbit contained in the local block. -/
theorem primeVertexBlock_maximal_invariant {B N : ℕ} (p : Fin (B+3))
    (y : primeVertexCone B N p) :
    (∀ t : ℝ,primeConeFlow p t y∈primeVertexBlock B N p) ↔ y.val=0 := by
  constructor
  · intro hy
    funext q
    by_contra hq
    have hpos : 0<y.val q := lt_of_le_of_ne (y.property.1 q) (Ne.symm hq)
    have hqp : q≠p := fun h => hq (h ▸ y.property.2.1)
    have hr := primeVertexRate_ne_zero hqp
    let t := Real.log (2/y.val q)/primeVertexRate p q
    have he : (primeConeFlow p t y).val q=2 := by
      change Real.exp ((Real.log (2/y.val q)/primeVertexRate p q)*primeVertexRate p q)*y.val q=2
      rw [div_mul_cancel₀ _ hr,Real.exp_log (div_pos (by norm_num) hpos),div_mul_cancel₀ _ hpos.ne']
    have hb := primeVertexBlock_coordinate_le (primeConeFlow p t y) (hy t) q
    rw [he] at hb
    norm_num at hb
  · intro hy t
    have hz : (primeConeFlow p t y).val=0 := by
      funext q
      change Real.exp (t*primeVertexRate p q)*y.val q=0
      rw [hy,Pi.zero_apply,mul_zero]
    constructor <;> simp only [primeUpperMass,primeLowerMass,hz,Pi.zero_apply,sum_const_zero,zero_le_one]

/-- Positive time strictly increases nonzero unstable mass. -/
theorem primeConeFlow_upper_strict {B N : ℕ} (p : Fin (B+3)) (y : primeVertexCone B N p)
    (hu : 0<primeUpperMass p y.val) {t : ℝ} (ht : 0<t) :
    primeUpperMass p y.val<primeUpperMass p (primeConeFlow p t y).val := by
  have he : ∃ q∈univ.filter (p<·),0<y.val q := by
    by_contra h
    push Not at h
    have hz : primeUpperMass p y.val=0 := by
      apply sum_eq_zero
      intro q hq
      exact le_antisymm (h q hq) (y.property.1 q)
    linarith only [hu,hz]
  apply sum_lt_sum
  · intro q hq
    have hr := primeVertexRate_pos (mem_filter.mp hq).2
    have hw : 1<Real.exp (t*primeVertexRate p q) := by
      rw [←Real.exp_zero,Real.exp_lt_exp]
      exact mul_pos ht hr
    exact le_trans (by rw [one_mul]) (mul_le_mul_of_nonneg_right hw.le (y.property.1 q))
  · obtain ⟨q,hq,hy⟩ := he
    refine ⟨q,hq,?_⟩
    have hr := primeVertexRate_pos (mem_filter.mp hq).2
    have hw : 1<Real.exp (t*primeVertexRate p q) := by
      rw [←Real.exp_zero,Real.exp_lt_exp]
      exact mul_pos ht hr
    change y.val q<Real.exp (t*primeVertexRate p q)*y.val q
    simpa only [one_mul] using mul_lt_mul_of_pos_right hw hy

/-- Every point of the unstable boundary exits the block immediately forward. -/
theorem primeVertexExit_leaves {B N : ℕ} (p : Fin (B+3)) (y : primeVertexExit B N p)
    {t : ℝ} (ht : 0<t) : primeConeFlow p t y.val.val∉primeVertexBlock B N p := by
  intro h
  have hu : 0<primeUpperMass p y.val.val.val := by rw [y.property]; exact zero_lt_one
  have hs := primeConeFlow_upper_strict p y.val.val hu ht
  rw [y.property] at hs
  exact (not_lt_of_ge h.1) hs

#print axioms primeVertexBlock_maximal_invariant
#print axioms primeVertexExit_leaves


/-- The actual upper link: adjoining the apex must still satisfy the prime-product cutoff. -/
def primeUpperLinkFaces (B N : ℕ) (p : Fin (B+3)) : Finset (Finset (Fin (B+3))) :=
  univ.filter (fun S => (∀ q∈S,p<q) ∧ insert p S∈primeHeightFaces B N)

/-- The upper-link section of the exit block, in projective coordinates. -/
def primeExitSection (B N : ℕ) (p : Fin (B+3)) : Set (primeVertexCone B N p) :=
  {y | primeUpperMass p y.val=1 ∧ primeLowerMass p y.val=0}

theorem primeCone_lower_zero_coordinate {B N : ℕ} {p : Fin (B+3)}
    (y : primeVertexCone B N p) (hy : primeLowerMass p y.val=0) {q : Fin (B+3)} (hq : q≤p) :
    y.val q=0 := by
  rcases lt_or_eq_of_le hq with hq | hq
  · have hle : y.val q≤primeLowerMass p y.val :=
      single_le_sum (fun r _ => y.property.1 r) (mem_filter.mpr ⟨mem_univ q,hq⟩)
    rw [hy] at hle
    exact le_antisymm hle (y.property.1 q)
  · rw [hq,y.property.2.1]

theorem primeCone_sum_of_lower_zero {B N : ℕ} {p : Fin (B+3)}
    (y : primeVertexCone B N p) (hy : primeLowerMass p y.val=0) :
    ∑ q,y.val q=primeUpperMass p y.val := by
  symm
  apply sum_subset (filter_subset _ _)
  intro q _ hq
  have hqp : q≤p := le_of_not_gt (fun h => hq (mem_filter.mpr ⟨mem_univ q,h⟩))
  exact primeCone_lower_zero_coordinate y hy hqp

def primeExitSectionToLink {B N : ℕ} {p : Fin (B+3)} (y : primeExitSection B N p) :
    faceFamilySpace (primeUpperLinkFaces B N p) :=
  ⟨⟨y.val.val,y.val.property.1,(primeCone_sum_of_lower_zero y.val y.property.2).trans y.property.1⟩,by
    obtain ⟨S,hS,hpS,hyS⟩ := y.val.property.2.2
    let T := S.filter (p<·)
    refine mem_faceFamilySpace.mpr ⟨T,mem_filter.mpr ⟨mem_univ T,?_,?_⟩,?_⟩
    · intro q hq
      exact (mem_filter.mp hq).2
    · exact primeHeightFaces_down_closed B N S hS (insert p T)
        (insert_subset hpS (filter_subset _ _))
    · intro q hq
      change y.val.val q=0
      by_cases hqS : q∈S
      · have hqp : q≤p := le_of_not_gt (fun h => hq (mem_filter.mpr ⟨hqS,h⟩))
        exact primeCone_lower_zero_coordinate y.val y.property.2 hqp
      · exact hyS q hqS⟩

theorem primeUpperLink_zero_coordinate {B N : ℕ} {p : Fin (B+3)}
    (x : faceFamilySpace (primeUpperLinkFaces B N p)) {q : Fin (B+3)} (hq : q≤p) :
    x.val.val q=0 := by
  obtain ⟨S,hS,hx⟩ := mem_faceFamilySpace.mp x.property
  have hS' := (mem_filter.mp hS).2.1
  exact hx q (fun h => (not_lt_of_ge hq) (hS' q h))

def primeUpperLinkToCone {B N : ℕ} {p : Fin (B+3)}
    (x : faceFamilySpace (primeUpperLinkFaces B N p)) : primeVertexCone B N p :=
  ⟨x.val.val,x.val.property.1,primeUpperLink_zero_coordinate x le_rfl,by
    obtain ⟨S,hS,hx⟩ := mem_faceFamilySpace.mp x.property
    refine ⟨insert p S,(mem_filter.mp hS).2.2,mem_insert_self p S,?_⟩
    intro q hq
    exact hx q (fun h => hq (mem_insert_of_mem h))⟩

theorem primeUpperLinkToCone_lower {B N : ℕ} {p : Fin (B+3)}
    (x : faceFamilySpace (primeUpperLinkFaces B N p)) :
    primeLowerMass p (primeUpperLinkToCone x).val=0 := by
  apply sum_eq_zero
  intro q hq
  exact primeUpperLink_zero_coordinate x (mem_filter.mp hq).2.le

def primeUpperLinkToSection {B N : ℕ} {p : Fin (B+3)}
    (x : faceFamilySpace (primeUpperLinkFaces B N p)) : primeExitSection B N p :=
  ⟨primeUpperLinkToCone x,by
    refine ⟨?_,primeUpperLinkToCone_lower x⟩
    rw [←primeCone_sum_of_lower_zero _ (primeUpperLinkToCone_lower x)]
    exact x.val.property.2⟩

/-- The exit section is homeomorphic to the original arithmetic upper-link realization. -/
def primeExitSectionHomeomorph (B N : ℕ) (p : Fin (B+3)) :
    primeExitSection B N p ≃ₜ faceFamilySpace (primeUpperLinkFaces B N p) where
  toFun := primeExitSectionToLink
  invFun := primeUpperLinkToSection
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The link section embeds into the exit of the actual local block. -/
def primeExitSectionInclusion {B N : ℕ} {p : Fin (B+3)} (y : primeExitSection B N p) :
    primeVertexExit B N p :=
  ⟨⟨y.val,by constructor <;> simp only [y.property.1,y.property.2,le_refl,zero_le_one]⟩,
    y.property.1⟩

def primeExitRetraction {B N : ℕ} (p : Fin (B+3)) (y : primeVertexExit B N p) :
    primeExitSection B N p :=
  ⟨(primeExitStableContraction p 1 y).val.val,
    (primeExitStableContraction p 1 y).property,primeExitStableContraction_one_lower p y⟩

theorem primeExitStableContraction_fixes_section {B N : ℕ} (p : Fin (B+3)) (t : unitInterval)
    (y : primeExitSection B N p) :
    primeExitStableContraction p t (primeExitSectionInclusion y)=primeExitSectionInclusion y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  change (if q<p then 1-(t:ℝ) else 1)*y.val.val q=y.val.val q
  by_cases hq : q<p
  · rw [primeCone_lower_zero_coordinate y.val y.property.2 hq.le,mul_zero]
  · rw [if_neg hq,one_mul]

#print axioms primeExitSectionHomeomorph
#print axioms primeExitStableContraction_fixes_section

/-- Closedness of the arithmetic support condition in projective coordinates. -/
theorem isClosed_primeVertexCone (B N : ℕ) (p : Fin (B+3)) :
    IsClosed (primeVertexCone B N p) := by
  let C : Finset (Fin (B+3)) → Set (Fin (B+3) → ℝ) :=
    fun S => {y | ∀ q∉S,y q=0}
  have hC : ∀ S,IsClosed (C S) := by
    intro S
    simpa only [C,Set.setOf_forall] using
      (isClosed_iInter (fun q : Fin (B+3) => isClosed_iInter (fun _ : q∉S =>
        isClosed_eq (continuous_apply q : Continuous (fun y : Fin (B+3) → ℝ => y q))
          (continuous_const : Continuous (fun _ : Fin (B+3) → ℝ => (0:ℝ))))))
  let T := (primeHeightFaces B N).filter (p∈·)
  have he : primeVertexCone B N p=
      {y | ∀ q,0≤y q} ∩ {y | y p=0} ∩ ⋃ S : T,C S.val := by
    ext y
    simp only [primeVertexCone,T,C,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iUnion,
      Subtype.exists,mem_filter,exists_prop]
    constructor
    · rintro ⟨hn,hp,S,hS,hpS,hy⟩
      exact ⟨⟨hn,hp⟩,S,⟨hS,hpS⟩,hy⟩
    · rintro ⟨⟨hn,hp⟩,S,⟨hS,hpS⟩,hy⟩
      exact ⟨hn,hp,S,hS,hpS,hy⟩
  rw [he]
  have hn : IsClosed {y : Fin (B+3) → ℝ | ∀q,0≤y q} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun q : Fin (B+3) => isClosed_le
        (continuous_const : Continuous (fun _ : Fin (B+3) → ℝ => (0:ℝ))) (continuous_apply q))
  exact (hn.inter (isClosed_eq (continuous_apply p) continuous_const)).inter
    (isClosed_iUnion_of_finite (fun S : T => hC S.val))

theorem primeUpperMass_continuous (B : ℕ) (p : Fin (B+3)) : Continuous (primeUpperMass p) :=
  continuous_finsetSum _ (fun q _ => continuous_apply q)

theorem primeLowerMass_continuous (B : ℕ) (p : Fin (B+3)) : Continuous (primeLowerMass p) :=
  continuous_finsetSum _ (fun q _ => continuous_apply q)

/-- The local block is compact in its actual cone topology. -/
theorem isCompact_primeVertexBlock (B N : ℕ) (p : Fin (B+3)) :
    IsCompact (primeVertexBlock B N p) := by
  have hc : IsClosed {y : Fin (B+3) → ℝ |
      y∈primeVertexCone B N p ∧ primeUpperMass p y≤1 ∧ primeLowerMass p y≤1} :=
    (isClosed_primeVertexCone B N p).inter
      ((isClosed_le (primeUpperMass_continuous B p) continuous_const).inter
        (isClosed_le (primeLowerMass_continuous B p) continuous_const))
  have hb : {y : Fin (B+3) → ℝ |
      y∈primeVertexCone B N p ∧ primeUpperMass p y≤1 ∧ primeLowerMass p y≤1} ⊆
      Set.Icc 0 1 := by
    intro y hy
    refine ⟨hy.1.1,?_⟩
    intro q
    exact primeVertexBlock_coordinate_le ⟨y,hy.1⟩ hy.2 q
  have hk := (isCompact_Icc : IsCompact (Set.Icc (0 : Fin (B+3) → ℝ) 1)).of_isClosed_subset hc hb
  have he : (Subtype.val : primeVertexCone B N p → Fin (B+3) → ℝ) ''
      primeVertexBlock B N p={y | y∈primeVertexCone B N p ∧
        primeUpperMass p y≤1 ∧ primeLowerMass p y≤1} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,hx⟩
    · intro hy
      exact ⟨⟨y,hy.1⟩,hy.2,rfl⟩
  rw [←he] at hk
  letI : CompactSpace ((Subtype.val : primeVertexCone B N p → Fin (B+3) → ℝ) ''
      primeVertexBlock B N p) := isCompact_iff_compactSpace.mp hk
  let f : ((Subtype.val : primeVertexCone B N p → Fin (B+3) → ℝ) ''
      primeVertexBlock B N p) → primeVertexCone B N p := fun y =>
        ⟨y.val,by obtain ⟨x,_,hx⟩ := y.property; exact hx ▸ x.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have him : f '' Set.univ=primeVertexBlock B N p := by
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩
      obtain ⟨z,hz,heq⟩ := y.property
      have hz' : f y=z := Subtype.ext heq.symm
      rw [hz']
      exact hz
    · intro hx
      exact ⟨⟨x.val,⟨x,hx,rfl⟩⟩,Set.mem_univ _,rfl⟩
  rw [←him]
  exact isCompact_univ.image hf

#print axioms isCompact_primeVertexBlock


/-- The arithmetic apex belongs to the cone exactly as its prime vertex does. -/
def primeConeApex {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime) (hpN : p.val≤N) :
    primeVertexCone B N p :=
  ⟨0,fun _ => le_refl 0,rfl,{p},mem_primeHeightFaces.mpr
    ⟨fun q hq => by simpa only [mem_singleton.mp hq] using hp,by simpa only [prod_singleton] using hpN⟩,
    mem_singleton_self p,fun _ _ => rfl⟩

/-- The isolated invariant apex lies in the interior of the local block. -/
theorem primeConeApex_mem_interior {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime) (hpN : p.val≤N) :
    primeConeApex p hp hpN∈interior (primeVertexBlock B N p) := by
  let U : Set (primeVertexCone B N p) :=
    {y | primeUpperMass p y.val<1 ∧ primeLowerMass p y.val<1}
  have hU : IsOpen U :=
    (isOpen_lt ((primeUpperMass_continuous B p).comp continuous_subtype_val) continuous_const).inter
      (isOpen_lt ((primeLowerMass_continuous B p).comp continuous_subtype_val) continuous_const)
  have hx : primeConeApex p hp hpN∈U := by
    constructor <;> simp only [primeUpperMass,primeLowerMass,primeConeApex,Pi.zero_apply,
      sum_const_zero,zero_lt_one]
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hx) (fun _ h => ⟨h.1.le,h.2.le⟩))

theorem primeConeFlow_upper_mono {B N : ℕ} (p : Fin (B+3)) (y : primeVertexCone B N p)
    {s t : ℝ} (hst : s≤t) :
    primeUpperMass p (primeConeFlow p s y).val≤primeUpperMass p (primeConeFlow p t y).val := by
  apply sum_le_sum
  intro q hq
  change Real.exp (s*primeVertexRate p q)*y.val q≤Real.exp (t*primeVertexRate p q)*y.val q
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hst (primeVertexRate_pos (mem_filter.mp hq).2).le)) (y.property.1 q)

theorem primeConeFlow_lower_antitone {B N : ℕ} (p : Fin (B+3)) (y : primeVertexCone B N p)
    {s t : ℝ} (hst : s≤t) :
    primeLowerMass p (primeConeFlow p t y).val≤primeLowerMass p (primeConeFlow p s y).val := by
  apply sum_le_sum
  intro q hq
  change Real.exp (t*primeVertexRate p q)*y.val q≤Real.exp (s*primeVertexRate p q)*y.val q
  have hr : primeVertexRate p q≤0 := by
    have h := primeVertexRate_pos (mem_filter.mp hq).2
    unfold primeVertexRate at h ⊢
    linarith only [h]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_right hst hr)) (y.property.1 q)

/-- Every escaping forward orbit crosses the designated exit before leaving the block. -/
theorem primeVertexBlock_exit_crossing {B N : ℕ} (p : Fin (B+3))
    (y : primeVertexCone B N p) (hy : y∈primeVertexBlock B N p)
    {t : ℝ} (ht : 0<t) (hout : primeConeFlow p t y∉primeVertexBlock B N p) :
    ∃ s∈Set.Icc 0 t,
      primeUpperMass p (primeConeFlow p s y).val=1 ∧
      ∀ r∈Set.Icc 0 s,primeConeFlow p r y∈primeVertexBlock B N p := by
  have hl : primeLowerMass p (primeConeFlow p t y).val≤1 := by
    have h := primeConeFlow_lower_antitone p y ht.le
    rw [primeConeFlow_zero] at h
    exact h.trans hy.2
  have hu : 1<primeUpperMass p (primeConeFlow p t y).val := by
    exact lt_of_not_ge (fun h => hout ⟨h,hl⟩)
  have hc : Continuous (fun s : ℝ => primeUpperMass p (primeConeFlow p s y).val) :=
    (primeUpperMass_continuous B p).comp (continuous_subtype_val.comp
      ((primeConeFlow_continuous B N p).comp (continuous_id.prodMk continuous_const)))
  have h0 : primeUpperMass p (primeConeFlow p 0 y).val≤1 := by
    rw [primeConeFlow_zero]
    exact hy.1
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc ht.le hc.continuousOn ⟨h0,hu.le⟩
  change primeUpperMass p (primeConeFlow p s y).val=1 at hse
  refine ⟨s,hs,hse,?_⟩
  intro r hr
  constructor
  · have h := primeConeFlow_upper_mono p y hr.2
    rwa [hse] at h
  · have h := primeConeFlow_lower_antitone p y hr.1
    rw [primeConeFlow_zero] at h
    exact h.trans hy.2

/-- Relative positive invariance of the exit: a positive orbit cannot stay in the block. -/
theorem primeVertexExit_relative_positive_invariant {B N : ℕ} (p : Fin (B+3))
    (y : primeVertexExit B N p) {t : ℝ} (ht : 0≤t)
    (hstay : ∀ r∈Set.Icc 0 t,primeConeFlow p r y.val.val∈primeVertexBlock B N p) : t=0 := by
  by_contra ht0
  exact primeVertexExit_leaves p y (lt_of_le_of_ne ht (Ne.symm ht0)) (hstay t ⟨ht,le_rfl⟩)

#print axioms primeConeApex_mem_interior
#print axioms primeVertexBlock_exit_crossing
#print axioms primeVertexExit_relative_positive_invariant

/-- Radial contraction stays within every allowed prime support and both mass bounds. -/
def primeBlockRadialContraction {B N : ℕ} (p : Fin (B+3)) (t : unitInterval)
    (y : primeVertexBlock B N p) : primeVertexBlock B N p := by
  let z : primeVertexCone B N p := ⟨fun q => (1-(t:ℝ))*y.val.val q,by
    refine ⟨fun q => mul_nonneg (sub_nonneg.mpr t.property.2) (y.val.property.1 q),?_,?_⟩
    · dsimp only
      rw [y.val.property.2.1,mul_zero]
    · obtain ⟨S,hS,hp,hy⟩ := y.val.property.2.2
      exact ⟨S,hS,hp,fun q hq => by dsimp only; rw [hy q hq,mul_zero]⟩⟩
  refine ⟨z,?_,?_⟩
  · change (∑ q∈univ.filter (p<·),(1-(t:ℝ))*y.val.val q)≤1
    rw [←mul_sum]
    exact (mul_le_of_le_one_left (sum_nonneg (fun q _ => y.val.property.1 q))
      (by linarith only [t.property.1])).trans y.property.1
  · change (∑ q∈univ.filter (·<p),(1-(t:ℝ))*y.val.val q)≤1
    rw [←mul_sum]
    exact (mul_le_of_le_one_left (sum_nonneg (fun q _ => y.val.property.1 q))
      (by linarith only [t.property.1])).trans y.property.2

def primeBlockApex {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime) (hpN : p.val≤N) :
    primeVertexBlock B N p :=
  ⟨primeConeApex p hp hpN,by
    constructor <;> simp only [primeUpperMass,primeLowerMass,primeConeApex,Pi.zero_apply,
      sum_const_zero,zero_le_one]⟩

/-- The local block contracts to its isolated arithmetic vertex. -/
def primeBlockContraction {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime) (hpN : p.val≤N) :
    (ContinuousMap.id (primeVertexBlock B N p)).Homotopy
      (ContinuousMap.const _ (primeBlockApex p hp hpN)) where
  toFun z := primeBlockRadialContraction p z.1 z.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro q
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply q).comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))
  map_zero_left y := by
    apply Subtype.ext
    apply Subtype.ext
    funext q
    change (1-((0:unitInterval):ℝ))*y.val.val q=y.val.val q
    simp only [show ((0:unitInterval):ℝ)=0 from rfl,sub_zero,one_mul]
  map_one_left y := by
    apply Subtype.ext
    apply Subtype.ext
    funext q
    change (1-((1:unitInterval):ℝ))*y.val.val q=0
    simp only [show ((1:unitInterval):ℝ)=1 from rfl,sub_self,zero_mul]

#print axioms primeBlockContraction


def primeExitInclusionMap (B N : ℕ) (p : Fin (B+3)) :
    C(primeExitSection B N p,primeVertexExit B N p) :=
  ⟨primeExitSectionInclusion,(continuous_subtype_val.subtype_mk _).subtype_mk _⟩

def primeExitRetractionMap (B N : ℕ) (p : Fin (B+3)) :
    C(primeVertexExit B N p,primeExitSection B N p) :=
  ⟨primeExitRetraction p,by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_subtype_val).comp
      ((primeExitStableContraction_continuous B N p).comp
        (continuous_const.prodMk continuous_id))⟩

/-- A strong deformation retraction of the exit onto its arithmetic link section. -/
def primeExitDeformation (B N : ℕ) (p : Fin (B+3)) :
    (ContinuousMap.id (primeVertexExit B N p)).Homotopy
      ((primeExitInclusionMap B N p).comp (primeExitRetractionMap B N p)) where
  toFun z := primeExitStableContraction p z.1 z.2
  continuous_toFun := primeExitStableContraction_continuous B N p
  map_zero_left := primeExitStableContraction_zero p
  map_one_left _ := rfl

/-- The actual exit is homotopy equivalent to the actual upper-link realization. -/
def primeExitLinkHomotopyEquiv (B N : ℕ) (p : Fin (B+3)) :
    primeVertexExit B N p ≃ₕ faceFamilySpace (primeUpperLinkFaces B N p) :=
  ({toFun := primeExitRetractionMap B N p
    invFun := primeExitInclusionMap B N p
    left_inv := ⟨(primeExitDeformation B N p).symm⟩
    right_inv := by
      have he : (primeExitRetractionMap B N p).comp (primeExitInclusionMap B N p)=
          ContinuousMap.id _ := by
        ext y : 1
        apply Subtype.ext
        exact congrArg (fun z : primeVertexExit B N p => z.val.val)
          (primeExitStableContraction_fixes_section p 1 y)
      rw [he]} : primeVertexExit B N p ≃ₕ primeExitSection B N p).trans
        (primeExitSectionHomeomorph B N p).toHomotopyEquiv

theorem primeVertexBlock_contractible {B N : ℕ} (p : Fin (B+3))
    (hp : p.val.Prime) (hpN : p.val≤N) : ContractibleSpace (primeVertexBlock B N p) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨primeBlockApex p hp hpN,⟨primeBlockContraction p hp hpN⟩⟩

#print axioms primeExitLinkHomotopyEquiv
#print axioms primeVertexBlock_contractible


/-- The forward exit is closed in the compact local block. -/
theorem isClosed_primeVertexExit (B N : ℕ) (p : Fin (B+3)) :
    IsClosed (primeVertexExit B N p) :=
  isClosed_eq ((primeUpperMass_continuous B p).comp
    (continuous_subtype_val.comp continuous_subtype_val)) continuous_const

/-- The exit is compact, including when it is empty. -/
theorem isCompact_primeVertexExit (B N : ℕ) (p : Fin (B+3)) :
    IsCompact (primeVertexExit B N p) := by
  letI : CompactSpace (primeVertexBlock B N p) :=
    isCompact_iff_compactSpace.mp (isCompact_primeVertexBlock B N p)
  exact (isClosed_primeVertexExit B N p).isCompact

#print axioms isCompact_primeVertexExit

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
