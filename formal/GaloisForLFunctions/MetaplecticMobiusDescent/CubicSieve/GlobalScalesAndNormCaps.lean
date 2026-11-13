/-
Global scales and norm caps adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.SecondPassNormalizedMass

/-!
# Global scales and norm caps

Global norm caps, bin triples and the row-scale floor of the descendant rows. The concrete
lattice cutoff gives polynomial row bounds, coefficients are constant on logarithmic bins, and
the truncated first source keeps radial decay.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
section
lemma parity_pair_norm_bounds (s u : Ideal O) (B : ℝ) (hB : 0<B)
    (hs : s≠0) (hu : u≠0)
    (h : (Ideal.absNorm u : ℝ)^2*Ideal.absNorm s≤B^2) :
    (Ideal.absNorm s : ℝ)≤B^2 ∧ (Ideal.absNorm u : ℝ)≤B/Real.sqrt (Ideal.absNorm s) := by
  have hs1 : 1≤(Ideal.absNorm s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hs (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu1 : 1≤(Ideal.absNorm u : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hu (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs0 : 0<(Ideal.absNorm s : ℝ) := by linarith
  have hsqrt : 0<Real.sqrt (Ideal.absNorm s : ℝ) := Real.sqrt_pos.mpr hs0
  refine ⟨(le_mul_of_one_le_left hs0.le (one_le_pow₀ hu1)).trans h,?_⟩
  apply (le_div_iff₀ hsqrt).mpr
  have hh : ((Ideal.absNorm u : ℝ)*Real.sqrt (Ideal.absNorm s : ℝ))^2≤B^2 := by
    simpa only [mul_pow,Real.sq_sqrt hs0.le] using h
  nlinarith [mul_nonneg (Nat.cast_nonneg (Ideal.absNorm u)) hsqrt.le]

lemma parity_pair_fiber_count (S : Finset (Ideal O × Ideal O)) (B : ℝ) (hB : 0<B)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2)
    (s : Ideal O) (hs : s∈S.image Prod.fst) :
    ((S.filter (fun x => x.1=s)).card : ℝ)≤descentLatticeConstant*B/Real.sqrt (Ideal.absNorm s) := by
  have hcontrol := descentLatticeConstant_pos
  obtain ⟨x,hx,hxs⟩ := Finset.mem_image.mp hs
  have hnx := parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2
  have hu1 : 1≤(Ideal.absNorm x.2 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (hS x hx).2.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤B/Real.sqrt (Ideal.absNorm s) := by simpa only [hxs] using hu1.trans hnx.2
  let T := S.filter (fun x => x.1=s)
  have hi : Set.InjOn (fun x : Ideal O × Ideal O => x.2) (↑T : Set (Ideal O × Ideal O)) := by
    intro x hx y hy he
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) he
  have hcount := descent_ideal_count (T.image Prod.snd)
    (B/Real.sqrt (Ideal.absNorm s)) hscale (fun u hu => by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      exact (hS x (Finset.mem_filter.mp hx).1).2.1) (fun u hu => by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      have hn := parity_pair_norm_bounds x.1 x.2 B hB (hS x (Finset.mem_filter.mp hx).1).1
        (hS x (Finset.mem_filter.mp hx).1).2.1 (hS x (Finset.mem_filter.mp hx).1).2.2
      simpa only [(Finset.mem_filter.mp hx).2] using hn.2)
  rw [Finset.card_image_iff.mpr hi] at hcount
  simpa only [mul_div_assoc] using hcount

theorem parity_ideal_pair_count (S : Finset (Ideal O × Ideal O)) (B H : ℝ)
    (hB : 0<B) (hH : 0≤H)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2)
    (hactive : ∀ x∈S,(Ideal.absNorm x.1 : ℝ)≤H^2) :
    (S.card : ℝ)≤descentLatticeConstant^2*Real.exp 1*B*H*(normLogBin (B^2)+1 : ℝ) := by
  have hcontrol := descentLatticeConstant_pos
  let A := S.image Prod.fst
  have hA (s : Ideal O) (hs : s∈A) : s≠0 ∧ (Ideal.absNorm s : ℝ)≤B^2 ∧ (Ideal.absNorm s : ℝ)≤H^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hS x hx).1,(parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2).1,hactive x hx⟩
  have he : (S.card : ℝ)=∑s∈A,((S.filter (fun x => x.1=s)).card : ℝ) := by
    calc
      _ = ∑_x∈S,(1 : ℝ) := by simp
      _ = ∑s∈A,∑_x∈S.filter (fun x => x.1=s),(1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem Prod.fst hx) _).symm
      _ = _ := by simp
  rw [he]
  have hpoint (s : Ideal O) (hs : s∈A) :
      1/Real.sqrt (Ideal.absNorm s : ℝ)≤H/(Ideal.absNorm s : ℝ) := by
    have hs0 : 0<(Ideal.absNorm s : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun hz => (hA s hs).1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hroot : 0<Real.sqrt (Ideal.absNorm s : ℝ) := Real.sqrt_pos.mpr hs0
    have hrootle : Real.sqrt (Ideal.absNorm s : ℝ)≤H := by nlinarith [Real.sq_sqrt hs0.le,(hA s hs).2.2]
    apply (div_le_div_iff₀ hroot hs0).mpr
    nlinarith [Real.sq_sqrt hs0.le]
  calc
    _ ≤ ∑s∈A,descentLatticeConstant*B/Real.sqrt (Ideal.absNorm s) :=
      Finset.sum_le_sum (fun s hs => parity_pair_fiber_count S B hB hS s hs)
    _ ≤ ∑s∈A,(descentLatticeConstant*B*H)*(1/(Ideal.absNorm s : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have h := mul_le_mul_of_nonneg_left (hpoint s hs) (by positivity : 0≤descentLatticeConstant*B)
      convert h using 1 <;> ring
    _ = (descentLatticeConstant*B*H)*∑s∈A,1/(Ideal.absNorm s : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (descentLatticeConstant*B*H)*(descentLatticeConstant*Real.exp 1*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (descent_ideal_inverse_sum A (B^2) (fun s hs => (hA s hs).1)
        (fun s hs => (hA s hs).2.1)) (by positivity)
    _ = _ := by ring

open Eisenstein
open FirstPassCubeLabels (primeProduct aLabel squarefreeLabel cubeActiveSupport)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cubeParityKey_norm_product (x : CubeCoordinates ι) :
    (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1 =
      ‖ringComplex (primeProduct p x.support x.leftExponent)‖^2*
        ‖ringComplex (primeProduct p x.support x.rightExponent)‖^2 := by
  have h := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (cubeParityKey_product p x)
  simpa only [cubeProductIdeal,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,
    ←ringComplex_norm_sq_eq_absNorm_span] using h.symm

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cubeParityKey_active_bound (x : CubeCoordinates ι) (H : ℝ)
    (ha : ‖ringComplex (∏ i∈cubeActiveSupport x.support
      (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤H) :
    (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤H^2 := by
  have h := squarefreeLabel_active_bound p hp x.support
    (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit
  change ‖ringComplex _‖^2≤‖ringComplex _‖^2 at h
  exact (show (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤‖ringComplex
    (∏ i∈cubeActiveSupport x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖^2 from
    by simpa only [cubeParityKey,←ringComplex_norm_sq_eq_absNorm_span] using h).trans
      (pow_le_pow_left₀ (norm_nonneg _) ha 2)

end

theorem cube_coordinates_parity_count (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (CubeCoordinates ι)) (B H : ℝ),
      1≤B → 0≤H → (∀ x∈s,x.Admissible) →
      (∀ x∈s,‖ringComplex (primeProduct p x.support x.leftExponent)‖^2≤B) →
      (∀ x∈s,‖ringComplex (primeProduct p x.support x.rightExponent)‖^2≤B) →
      (∀ x∈s,‖ringComplex (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤H) →
      (s.card : ℝ)≤C*B^(1+ε)*H := by
  have hcontrol := descentLatticeConstant_pos
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/12) (by positivity)
  let C := D^3*(descentLatticeConstant^2*Real.exp 1)*(1+1/(ε/4))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ p hp _ hinj s B H hB hH hs hb1 hb2 ha
  have hB0 : 0<B := by linarith
  have hprod (x : CubeCoordinates ι) (hx : x∈s) :
      (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1≤B^2 := by
    rw [cubeParityKey_norm_product]
    simpa only [pow_two] using mul_le_mul (hb1 x hx) (hb2 x hx) (sq_nonneg _) hB0.le
  let Q := s.image (cubeParityKey p)
  have hQ (q : Ideal O × Ideal O) (hq : q∈Q) :
      q.1≠0 ∧ q.2≠0 ∧ (Ideal.absNorm q.2 : ℝ)^2*Ideal.absNorm q.1≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(cubeParityKey_ne_zero p hp x).1,(cubeParityKey_ne_zero p hp x).2,hprod x hx⟩
  have hQactive (q : Ideal O × Ideal O) (hq : q∈Q) : (Ideal.absNorm q.1 : ℝ)≤H^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact cubeParityKey_active_bound p hp x H (ha x hx)
  have hfiber (q : Ideal O × Ideal O) (hq : q∈Q) :
      ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤D^3*B^(ε/2) := by
    have hq0 := hQ q hq
    have hqprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq0.2.1) hq0.1
    have hc : ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤
        ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := by
      exact_mod_cast cubeParityKey_fiber_card p hp hinj (s.filter (fun x => cubeParityKey p x=q)) q
        hq0.1 hq0.2.1 (fun x hx => hs x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
    have hn : (Ideal.absNorm (q.2^2*q.1) : ℝ)≤B^2 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hq0.2.2
    calc
      _ ≤ ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := hc
      _ ≤ (D*(Ideal.absNorm (q.2^2*q.1) : ℝ)^(ε/12))^3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hqprod0) 3
      _ ≤ (D*(B^2)^(ε/12))^3 := by gcongr
      _ = D^3*B^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg B),
          ←Real.rpow_natCast,←Real.rpow_mul hB0.le]
        congr 1
        ring
  have hqcard := parity_ideal_pair_count Q B H hB0 hH hQ hQactive
  have hlog := descent_normLogBin_small_power (ε/4) (by positivity) (B^2) (one_le_pow₀ hB)
  have hlog' : (normLogBin (B^2)+1 : ℝ)≤(1+1/(ε/4))*B^(ε/2) := by
    convert hlog using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le]
    congr 2
    ring
  have hsum : (s.card : ℝ)=∑q∈Q,((s.filter (fun x => cubeParityKey p x=q)).card : ℝ) := by
    calc
      _ = ∑_x∈s,(1 : ℝ) := by simp
      _ = ∑q∈Q,∑_x∈s.filter (fun x => cubeParityKey p x=q),(1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeParityKey p) hx) _).symm
      _ = _ := by simp
  rw [hsum]
  calc
    _ ≤ ∑_q∈Q,D^3*B^(ε/2) := Finset.sum_le_sum hfiber
    _ = (Q.card : ℝ)*(D^3*B^(ε/2)) := by simp
    _ ≤ (descentLatticeConstant^2*Real.exp 1*B*H*(normLogBin (B^2)+1 : ℝ))*(D^3*B^(ε/2)) := by gcongr
    _ ≤ (descentLatticeConstant^2*Real.exp 1*B*H*((1+1/(ε/4))*B^(ε/2)))*(D^3*B^(ε/2)) := by gcongr
    _ = C*B^(1+ε)*H := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      have he : B^(ε/2)*B^(ε/2)=B^ε := by rw [←Real.rpow_add hB0]; congr 1; ring
      dsimp [C]
      calc
        _ = D^3*(descentLatticeConstant^2*Real.exp 1)*(1+1/(ε/4))*B*(B^(ε/2)*B^(ε/2))*H := by ring
        _ = _ := by rw [he]; ring

end

section
open Eisenstein
open FirstPassCubeLabels (primeProduct cubeActiveSupport)

theorem parity_ideal_pair_inverse_sqrt_sum (S : Finset (Ideal O × Ideal O)) (B : ℝ)
    (hB : 0<B)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2) :
    (∑q∈S,1/Real.sqrt (Ideal.absNorm q.1 : ℝ))≤
      descentLatticeConstant^2*Real.exp 1*B*(normLogBin (B^2)+1 : ℝ) := by
  have hcontrol := descentLatticeConstant_pos
  let A := S.image Prod.fst
  have hA (s : Ideal O) (hs : s∈A) : s≠0 ∧ (Ideal.absNorm s : ℝ)≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hS x hx).1,(parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2).1⟩
  have he : (∑q∈S,1/Real.sqrt (Ideal.absNorm q.1 : ℝ))=
      ∑s∈A,((S.filter (fun x => x.1=s)).card : ℝ)/Real.sqrt (Ideal.absNorm s : ℝ) := by
    calc
      _ = ∑s∈A,∑q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm q.1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem Prod.fst hx) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        have h : (∑q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm q.1 : ℝ))=
            ∑_q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm s : ℝ) :=
          Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2])
        rw [h]
        simp [div_eq_mul_inv]
  rw [he]
  calc
    _ ≤ ∑s∈A,descentLatticeConstant*B/(Ideal.absNorm s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      have hpos : 0<(Ideal.absNorm s : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (fun hz => (hA s hs).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      calc
        _ ≤ (descentLatticeConstant*B/Real.sqrt (Ideal.absNorm s : ℝ))/Real.sqrt (Ideal.absNorm s : ℝ) :=
          div_le_div_of_nonneg_right (parity_pair_fiber_count S B hB hS s hs) (Real.sqrt_nonneg _)
        _ = _ := by rw [div_div,←pow_two,Real.sq_sqrt hpos.le]
    _ = (descentLatticeConstant*B)*∑s∈A,1/(Ideal.absNorm s : ℝ) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs; ring
    _ ≤ (descentLatticeConstant*B)*(descentLatticeConstant*Real.exp 1*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (descent_ideal_inverse_sum A (B^2)
        (fun s hs => (hA s hs).1) (fun s hs => (hA s hs).2)) (by positivity)
    _ = _ := by ring

theorem cube_coordinates_inverse_active_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (CubeCoordinates ι)) (B : ℝ),
      1≤B → (∀ x∈s,x.Admissible) →
      (∀ x∈s,‖ringComplex (primeProduct p x.support x.leftExponent)‖^2≤B) →
      (∀ x∈s,‖ringComplex (primeProduct p x.support x.rightExponent)‖^2≤B) →
      (∑x∈s,1/‖ringComplex (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖)≤C*B^(1+ε) := by
  have hcontrol := descentLatticeConstant_pos
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/12) (by positivity)
  let C := D^3*(descentLatticeConstant^2*Real.exp 1)*(1+1/(ε/4))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ p hp _ hinj s B hB hs hb1 hb2
  have hB0 : 0<B := by linarith
  have hprod (x : CubeCoordinates ι) (hx : x∈s) :
      (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1≤B^2 := by
    rw [cubeParityKey_norm_product]
    simpa only [pow_two] using mul_le_mul (hb1 x hx) (hb2 x hx) (sq_nonneg _) hB0.le
  let Q := s.image (cubeParityKey p)
  have hQ (q : Ideal O × Ideal O) (hq : q∈Q) :
      q.1≠0 ∧ q.2≠0 ∧ (Ideal.absNorm q.2 : ℝ)^2*Ideal.absNorm q.1≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(cubeParityKey_ne_zero p hp x).1,(cubeParityKey_ne_zero p hp x).2,hprod x hx⟩
  have hfiber (q : Ideal O × Ideal O) (hq : q∈Q) :
      ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤D^3*B^(ε/2) := by
    have hq0 := hQ q hq
    have hqprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq0.2.1) hq0.1
    have hc : ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤
        ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := by
      exact_mod_cast cubeParityKey_fiber_card p hp hinj (s.filter (fun x => cubeParityKey p x=q)) q
        hq0.1 hq0.2.1 (fun x hx => hs x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
    have hn : (Ideal.absNorm (q.2^2*q.1) : ℝ)≤B^2 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hq0.2.2
    calc
      _ ≤ ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := hc
      _ ≤ (D*(Ideal.absNorm (q.2^2*q.1) : ℝ)^(ε/12))^3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hqprod0) 3
      _ ≤ (D*(B^2)^(ε/12))^3 := by gcongr
      _ = D^3*B^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg B),
          ←Real.rpow_natCast,←Real.rpow_mul hB0.le]
        congr 1
        ring
  have hlog := descent_normLogBin_small_power (ε/4) (by positivity) (B^2) (one_le_pow₀ hB)
  have hlog' : (normLogBin (B^2)+1 : ℝ)≤(1+1/(ε/4))*B^(ε/2) := by
    convert hlog using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le]
    congr 2
    ring
  have hpoint (x : CubeCoordinates ι) :
      1/‖ringComplex (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤
        1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) := by
    have hs0 : 0<(Ideal.absNorm (cubeParityKey p x).1 : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun hz => (cubeParityKey_ne_zero p hp x).1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have ha := cubeParityKey_active_bound p hp x _ le_rfl
    have hh : Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤
        ‖ringComplex (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖ := by
      nlinarith [Real.sq_sqrt hs0.le,norm_nonneg (ringComplex (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i))]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hs0) hh
  have he : (∑x∈s,1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ))=
      ∑q∈Q,((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)*(1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := by
    calc
      _ = ∑q∈Q,∑x∈s.filter (fun x => cubeParityKey p x=q),1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeParityKey p) hx) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have h := Finset.sum_congr rfl (fun x (hx : x∈s.filter (fun x => cubeParityKey p x=q)) =>
          show 1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ)=1/Real.sqrt (Ideal.absNorm q.1 : ℝ) by
            rw [(Finset.mem_filter.mp hx).2])
        rw [h]
        simp
  calc
    _ ≤ ∑x∈s,1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := he
    _ ≤ ∑q∈Q,(D^3*B^(ε/2))*(1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := by
      exact Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (by positivity))
    _ = (D^3*B^(ε/2))*(∑q∈Q,1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (D^3*B^(ε/2))*(descentLatticeConstant^2*Real.exp 1*B*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (parity_ideal_pair_inverse_sqrt_sum Q B hB0 hQ) (by positivity)
    _ ≤ (D^3*B^(ε/2))*(descentLatticeConstant^2*Real.exp 1*B*((1+1/(ε/4))*B^(ε/2))) := by gcongr
    _ = C*B^(1+ε) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      have he : B^(ε/2)*B^(ε/2)=B^ε := by rw [←Real.rpow_add hB0]; congr 1; ring
      dsimp [C]
      calc
        _ = D^3*(descentLatticeConstant^2*Real.exp 1)*(1+1/(ε/4))*B*(B^(ε/2)*B^(ε/2)) := by ring
        _ = _ := by rw [he]; ring

end

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def globalFirstCountKey (b : GlobalFirstData ι) : CubeCoordinates ι × Finset ι × Finset ι :=
  (b.cube,b.common,b.firstCommon)

def globalFirstDivisorTarget (q : CubeCoordinates ι × Finset ι × Finset ι) : Ideal O :=
  (∏i∈q.2.1,Ideal.span {p i})*(∏i∈q.1.support,Ideal.span {p i})

theorem globalFirstDivisorTarget_ne_zero (q : CubeCoordinates ι × Finset ι × Finset ι) :
    globalFirstDivisorTarget p q≠0 := by
  apply mul_ne_zero <;> exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalFirst_divisor_dvd_target (b : GlobalFirstData ι) (hb : GlobalFirstAdmissible b) :
    (∏i∈b.firstDivisor,Ideal.span {p i})∣globalFirstDivisorTarget p (globalFirstCountKey b) := by
  have h := Finset.prod_dvd_prod_of_subset b.firstDivisor (b.common∪b.cube.support)
    (fun i => (Ideal.span {p i} : Ideal O)) hb.2.2
  rw [Finset.prod_union hb.2.1] at h
  exact h

include hinj in
theorem globalFirst_divisor_fiber_card (s : Finset (GlobalFirstData ι))
    (q : CubeCoordinates ι × Finset ι × Finset ι)
    (hs : ∀b∈s,GlobalFirstAdmissible b) (hq : ∀b∈s,globalFirstCountKey b=q) :
    s.card≤(idealDivisors (globalFirstDivisorTarget p q)).card := by
  let D := idealDivisors (globalFirstDivisorTarget p q)
  let encode (b : s) : D := ⟨∏i∈b.val.firstDivisor,Ideal.span {p i},by
    apply (mem_idealDivisors (globalFirstDivisorTarget_ne_zero p q)).mpr
    simpa only [hq b.val b.property] using globalFirst_divisor_dvd_target p b.val (hs b.val b.property)⟩
  have hi : Function.Injective encode := by
    intro b c he
    have hd := primeIdealFamily_product_injective (fun i => Ideal.span {p i}) hinj (congrArg Subtype.val he)
    have hk := (hq b.val b.property).trans (hq c.val c.property).symm
    apply Subtype.ext
    exact GlobalFirstData.ext (congrArg Prod.fst hk) (congrArg (fun q => q.2.2) hk)
      (congrArg (fun q => q.2.1) hk) hd
  simpa only [Fintype.card_coe,D] using Fintype.card_le_of_injective encode hi

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalFirstDivisorTarget_norm_bound (b : GlobalFirstData ι) (B U : ℝ)
    (hB : 0≤B) (hU : 0≤U) (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    (Ideal.absNorm (globalFirstDivisorTarget p (globalFirstCountKey b)) : ℝ)≤U*B^2 := by
  have hrad := globalCube_radical_bound p hp B hB (b.append ⟨∅,∅,∅,1⟩) hb1 hb2
  change (Ideal.absNorm ((∏i∈b.common,Ideal.span {p i})*(∏i∈b.cube.support,Ideal.span {p i})) : ℝ)≤_
  rw [map_mul,Nat.cast_mul,←primeProductNorm_eq_ideal_norm,←primeProductNorm_eq_ideal_norm]
  exact mul_le_mul hc hrad (primeProductNorm_pos p hp _).le hU

include hinj in
theorem primeSupport_inverse_sum (s : Finset (Finset ι)) (U : ℝ)
    (hs : ∀S∈s,primeProductNorm p S≤U) :
    (∑S∈s,1/primeProductNorm p S)≤descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ) := by
  let f := fun S : Finset ι => ∏i∈S,(Ideal.span {p i} : Ideal O)
  have hi : Function.Injective f := primeIdealFamily_product_injective _ hinj
  have he : (∑S∈s,1/primeProductNorm p S)=∑I∈s.image f,1/(Ideal.absNorm I : ℝ) := by
    rw [Finset.sum_image (fun S _ T _ h => hi h)]
    exact Finset.sum_congr rfl (fun S hS => by rw [primeProductNorm_eq_ideal_norm])
  rw [he]
  apply descent_ideal_inverse_sum
  · intro I hI
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hI
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro I hI
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hI
    simpa only [f,←primeProductNorm_eq_ideal_norm] using hs S hS

end

theorem globalFirstData_harmonic_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (B U : ℝ),
      1≤B → 1≤U → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
        (1/‖ringComplex (∏i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))≤
        C*B^(1+ε)*(U*B^2)^ε*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))^2 := by
  have hcontrol := descentLatticeConstant_pos
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  obtain ⟨E,hE,hcube⟩ := cube_coordinates_inverse_active_sum ε hε
  refine ⟨D*E,mul_pos hD hE,?_⟩
  intro ι _ p hp _ hinj s B U hB hU hs hC ht hb1 hb2
  let Q := s.image globalFirstCountKey
  let cubes := s.image GlobalFirstData.cube
  let commons := s.image GlobalFirstData.common
  let firsts := s.image GlobalFirstData.firstCommon
  let weight := fun q : CubeCoordinates ι × Finset ι × Finset ι =>
    (1/primeProductNorm p q.2.1)*(1/primeProductNorm p q.2.2)*
      (1/‖ringComplex (∏i∈cubeActiveSupport q.1.support
        (fun i => q.1.leftExponent i+q.1.rightExponent i) q.1.leftBit q.1.rightBit,p i)‖)
  have hw (q : CubeCoordinates ι × Finset ι × Finset ι) : 0≤weight q := by
    have h1 := (primeProductNorm_pos p hp q.2.1).le
    have h2 := (primeProductNorm_pos p hp q.2.2).le
    dsimp [weight]
    positivity
  have hfiber (q : CubeCoordinates ι × Finset ι × Finset ι) (hq : q∈Q) :
      ((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)≤D*(U*B^2)^ε := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    have hc : ((s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b)).card : ℝ)≤
        ((idealDivisors (globalFirstDivisorTarget p (globalFirstCountKey b))).card : ℝ) := by
      exact_mod_cast globalFirst_divisor_fiber_card p hinj (s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b))
        (globalFirstCountKey b) (fun d hd => hs d (Finset.mem_filter.mp hd).1) (fun d hd => (Finset.mem_filter.mp hd).2)
    apply hc.trans ((hdiv _ (globalFirstDivisorTarget_ne_zero p _)).trans _)
    apply mul_le_mul_of_nonneg_left _ hD.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (globalFirstDivisorTarget_norm_bound p hp b B U (by linarith) (by linarith) (hC b hb) (hb1 b hb) (hb2 b hb)) hε.le
  have hsub : Q⊆cubes.product (commons.product firsts) := by
    intro q hq
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,Finset.mem_image_of_mem _ hb⟩⟩
  have he : (∑b∈s,weight (globalFirstCountKey b))=
      ∑q∈Q,((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)*weight q := by
    calc
      _ = ∑q∈Q,∑b∈s.filter (fun b => globalFirstCountKey b=q),weight (globalFirstCountKey b) :=
        (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_image_of_mem globalFirstCountKey hb) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have h := Finset.sum_congr rfl (fun b (hb : b∈s.filter (fun b => globalFirstCountKey b=q)) =>
          show weight (globalFirstCountKey b)=weight q by rw [(Finset.mem_filter.mp hb).2])
        rw [h]
        simp
  have hcube' := hcube p hp hinj cubes B hB (by
      intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact (hs b hb).1)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb1 b hb)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb2 b hb)
  have hC' := primeSupport_inverse_sum p hinj commons U (by
    intro C hCmem; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hCmem; exact hC b hb)
  have ht' := primeSupport_inverse_sum p hinj firsts U (by
    intro T hT; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hT; exact ht b hb)
  have hC0 : 0≤∑C∈commons,1/primeProductNorm p C :=
    Finset.sum_nonneg (fun C _ => one_div_nonneg.mpr (primeProductNorm_pos p hp C).le)
  have ht0 : 0≤∑T∈firsts,1/primeProductNorm p T :=
    Finset.sum_nonneg (fun T _ => one_div_nonneg.mpr (primeProductNorm_pos p hp T).le)
  change (∑b∈s,weight (globalFirstCountKey b))≤_
  rw [he]
  calc
    _ ≤ ∑q∈Q,(D*(U*B^2)^ε)*weight q := Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (hw q))
    _ = (D*(U*B^2)^ε)*∑q∈Q,weight q := (Finset.mul_sum _ _ _).symm
    _ ≤ (D*(U*B^2)^ε)*∑q∈cubes.product (commons.product firsts),weight q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw q)) (by positivity)
    _ = (D*(U*B^2)^ε)*
        ((∑x∈cubes,1/‖ringComplex (∏i∈cubeActiveSupport x.support
          (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖)*
          (∑C∈commons,1/primeProductNorm p C)*(∑T∈firsts,1/primeProductNorm p T)) := by
      congr 1
      simp only [Finset.product_eq_sprod,Finset.sum_product,weight]
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C hCmem
      ring
    _ ≤ (D*(U*B^2)^ε)*((E*B^(1+ε))*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))) := by
      gcongr
    _ = _ := by ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

theorem globalDiagonalPowers (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ B U : ℝ,1≤B → 1≤U →
      B^(ε/3)*(U*B^2)^(ε/3)*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))^2≤C*(B*U)^ε := by
  have hcontrol := descentLatticeConstant_pos
  let k : ℝ := descentLatticeConstant*Real.exp 1
  let C := k^2*(1+1/(ε/3))^2
  refine ⟨C,by dsimp [C,k]; positivity,?_⟩
  intro B U hB hU
  have hB0 : 0<B := by linarith
  have hU0 : 0<U := by linarith
  have hη : 0<ε/3 := by positivity
  have hlog := descent_normLogBin_small_power (ε/3) hη U hU
  have hBp : B^(ε/3)*(B^2)^(ε/3)=B^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le,←Real.rpow_add hB0]
    congr 1
    ring
  have hUp : U^(ε/3)*(U^(ε/3))^2=U^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le,←Real.rpow_add hU0]
    congr 1
    ring
  calc
    _ ≤ B^(ε/3)*(U*B^2)^(ε/3)*(k*((1+1/(ε/3))*U^(ε/3)))^2 := by
      dsimp [k]
      gcongr
    _ = k^2*(1+1/(ε/3))^2*(B^(ε/3)*(B^2)^(ε/3))*(U^(ε/3)*(U^(ε/3))^2) := by
      rw [Real.mul_rpow hU0.le (sq_nonneg B)]
      ring
    _ = C*(B*U)^ε := by rw [hBp,hUp,Real.mul_rpow hB0.le hU0.le]; dsimp [C]; ring

open Eisenstein
open FirstPassCubeLabels (primeProduct cubeActiveSupport)

theorem globalFirstDiagonalCost_parent_bound (ε : ℝ) (hε : 0<ε)
    (g W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Ψ : O →* ℂ) (m : O) (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U → ell*Real.exp M≤U →
      (∀z,‖Ψ z‖≤1) → (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      globalFirstDiagonalCost p hg pool s
        (fun b => ((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ))
        Ψ m g W ell side (globalFirstPooledRow p K ell B F side)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cg,hCg,hmass⟩ := full_uniform_normalized_second_mass g M hM
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  let P := Cd*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3
  have hP : 0≤P := by dsimp [P]; positivity
  refine ⟨P*Cp+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj pool s w Ψ m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨ hw hs hb1 hb2
  have hB0 : 0<B := by linarith
  let T := s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖ringComplex (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have ht (b : GlobalFirstData ι) (hb : b∈T) : b∈s := (Finset.mem_filter.mp hb).1
  have hsum := hcount p hp hinj T B U hB hU
    (fun b hb => hs b (ht b hb)) (fun b hb => (Finset.mem_filter.mp hb).2.1)
    (fun b hb => (Finset.mem_filter.mp hb).2.2)
    (fun b hb => hb1 b (ht b hb)) (fun b hb => hb2 b (ht b hb))
  change (∑b∈T,θ b)≤_ at hsum
  rw [globalFirstDiagonalCost_eq_supported p hp hg pool s _ Ψ m g W ell M U hell hM hellU side]
  change globalFirstDiagonalCost p hg pool T _ Ψ m g W ell side _≤_
  have hterm (b : GlobalFirstData ι) (hb : b∈T) :
      ‖((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ)‖*(primeProductNorm p b.firstCommon)⁻¹*
        (|globalFirstPooledRow p K ell B F side b| *‖paperRadialFourier W 0‖*
          globalFirstColumnMass p hg pool b Ψ m g ell side)≤
        (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := primeProductNorm_pos p hp b.firstCommon
    have hcpos := primeProductNorm_pos p hp b.common
    have hapos := primeProductNorm_pos p hp (b.cube.sideDivisor side)
    have hX : 0<globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon := by
      unfold globalFirstBlockColumnScale
      positivity
    have hm := hmass p hp hg hinj (globalFirstRawPool pool b) Ψ hΨ
      (m*globalFirstBadLabel p b) (globalFirstRetainedLabel p b)
      (∏ i ∈ b.firstDivisor, p i)
      (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) hX
    change globalFirstColumnMass p hg pool b Ψ m g ell side≤Cg at hm
    have hm0 : 0≤globalFirstColumnMass p hg pool b Ψ m g ell side :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hwb := hw b (ht b hb)
    have hwΓ := hwb.2
    rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hwb.1 hc),abs_of_pos hY]
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = (w b*‖paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by gcongr
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*(((Real.exp 1)^3*ell*B^2*F)*θ b) :=
        mul_le_mul_of_nonneg_left hsc' (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*(∑b∈T,θ b) := by
      unfold globalFirstDiagonalCost
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = P*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      dsimp [P]
      ring
    _ ≤ P*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ ≤ (P*Cp+1)*Γ*(ell*B^3*F)*(B*U)^ε := by
      calc
        _ = (P*Cp)*(Γ*(ell*B^3*F)*(B*U)^ε) := by ring
        _ ≤ (P*Cp+1)*(Γ*(ell*B^3*F)*(B*U)^ε) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

def SecondSourceSupport {ι : Type*} [DecidableEq ι]
    (p : ι → O) (X M : ℝ) (x : SecondExpansionData ι) : Prop :=
  Disjoint x.sourceCommon x.overlap ∧
    primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
/-- A nonzero normalized source is supported where its common and overlap norms fit the column scale. -/
theorem secondFixedExpansionTerm_zero_off_support
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ, ℂ))
    (X Y M : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (negative : Bool) (r : QuadraticRayRing) (ray s q : QuadraticRayRing × QuadraticRayRing)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hs : ¬SecondSourceSupport p X M x) :
    secondFixedExpansionTerm p hg F Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) W Y negative r ray s q x = 0 := by
  by_cases hd : Disjoint x.sourceCommon x.overlap
  · have hb : ¬primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M :=
      fun hb => hs ⟨hd,hb⟩
    have hz (N : Finset ι) :
        normalizedColumn p (fun A => g (columnLog p X A)) ((x.sourceCommon ∪ x.overlap) ∪ N) = 0 := by
      by_contra hn
      have hg0 : g (columnLog p X ((x.sourceCommon ∪ x.overlap) ∪ N)) ≠ 0 := by
        intro he
        exact hn (by simp only [normalizedColumn, he, zero_div])
      have hnorm := (primeProductNorm_mono p hp
        (show x.sourceCommon ∪ x.overlap ⊆ (x.sourceCommon ∪ x.overlap) ∪ N from Finset.subset_union_left)).trans
        (columnLog_norm_upper p hp X M hX _ ((le_abs_self _).trans (hgM _ hg0)))
      rw [primeProductNorm_union p _ _ hd] at hnorm
      exact hb hnorm
    unfold secondFixedExpansionTerm fixedChildKernelPair
    simp only [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro Q hQ
    have hcol : combinedFixedColumn p hg negative q.1 s.1
        (fun U => normalizedColumn p (fun A => g (columnLog p X A)) ((x.sourceCommon ∪ x.overlap) ∪ U)) N = 0 := by
      rw [combinedFixedColumn_test_factor, hz N, mul_zero]
    simp only [secondChildColumn, hcol, mul_zero, star_zero, zero_mul]
  · unfold secondFixedExpansionTerm
    rw [secondTotalWeight_zero_of_source_overlap p hg Ψ Ψ m c d x.frequency
      x.sourceCommon x.divisor x.overlap hE ray hd, mul_zero, zero_mul, zero_mul]

def globalFirstSupportedPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  (globalFirstExpansionPool pool s cutoff).filter (fun x =>
    SecondSourceSupport p (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) M x.source)

include hp in
theorem globalSecondFixedLiteralTerm_zero_off_support
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ))
    (ell M : ℝ) (hell : 0 < ell) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (side : Bool) (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : GlobalSecondData ι)
    (hE : x.source.divisor ⊆ x.source.sourceCommon)
    (hs : ¬SecondSourceSupport p
      (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) M x.source) :
    globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t Y ray s q x = 0 := by
  unfold globalSecondFixedLiteralTerm
  rw [secondFixedExpansionTerm_zero_off_support p hp hg _ _ _ _ _ _ _ _ _ M
    (div_pos (globalFirstColumnScale_pos p hp ell hell x side) (primeProductNorm_pos p hp _))
    (fun u hu => hgM u (firstCoreModeProfile_support g V side t u hu).1) side r ray s q x.source hE hs,
    mul_zero]

theorem globalFirstSupportedPool_admissible (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b ∈ s, GlobalFirstAdmissible b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x ∈ globalFirstSupportedPool p pool s cutoff ell M side) : GlobalSecondAdmissible x := by
  have hm := (mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1
  have hb := hs x.first hm.1
  have hE := ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.1
  exact ⟨hb.1,hE,hb.2.1,hb.2.2⟩

theorem globalFirstSupportedPool_frequency_ne_zero (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x ∈ globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side) :
    x.source.frequency ≠ 0 :=
  globalFirstExpansionPool_frequency_ne_zero pool s cutoff x (Finset.mem_filter.mp hx).1

theorem globalFirstTruncatedSource_eq_supported_fixed
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (s₀ : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ)) (ell M : ℝ) (hell : 0 < ell)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) :
    globalFirstTruncatedSource p hp hg pool s₀ w Ψ m g V W ell side r t Y cutoff =
      ∑ ray : QuadraticRayRing × QuadraticRayRing,
        ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
          ∑ x ∈ globalFirstSupportedPool p pool s₀ cutoff ell M side,
            w x.first * globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t Y ray s q x := by
  rw [globalFirstTruncatedSource_eq_normalized_fixed p hg hp hinj hc hpr pool s₀ w Ψ m g V W ell hell]
  apply Finset.sum_congr rfl
  intro ray _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hx hn
  have hs : ¬SecondSourceSupport p
      (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) M x.source :=
    fun h => hn (Finset.mem_filter.mpr ⟨hx,h⟩)
  have hE := ((mem_secondExpansionPool _ _ x.source).mp
    ((mem_globalFirstExpansionPool pool s₀ cutoff x).mp hx).2).2.1
  rw [globalSecondFixedLiteralTerm_zero_off_support p hp hg pool Ψ m g V W ell M hell hgM
    side r t Y ray s q x hE hs, mul_zero]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

private theorem five_factor_bounds (a b c d e : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) :
    a ≤ a*b*c*d*e ∧ b ≤ a*b*c*d*e ∧ c ≤ a*b*c*d*e ∧ d ≤ a*b*c*d*e ∧ e ≤ a*b*c*d*e := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      a = a*1*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      b = 1*b*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      c = 1*1*c*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      d = 1*1*1*d*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      e = 1*1*1*1*e := by ring
      _ ≤ _ := by gcongr

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalSupported_small_norms (ell M : ℝ) (_hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    primeProductNorm p (x.cube.sideDivisor side) ≤ ell*Real.exp M ∧
    primeProductNorm p x.common ≤ ell*Real.exp M ∧
    primeProductNorm p x.firstCommon ≤ ell*Real.exp M ∧
    primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.divisor ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hg := primeProductNorm_ge_one p hp x.source.sourceCommon
  have hv := primeProductNorm_ge_one p hp x.source.overlap
  have hden : 0 < primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon := by positivity
  have heq : (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)*Real.exp M =
      (ell*Real.exp M)/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon) := by
    unfold globalFirstColumnScale
    ring
  have hprod := (le_div_iff₀ hden).mp (hs.2.trans_eq heq)
  have hprod' : primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*
      primeProductNorm p x.firstCommon*primeProductNorm p x.source.sourceCommon*primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hprod
  obtain ⟨ha',hc',ht',hg',hv'⟩ := five_factor_bounds _ _ _ _ _ ha hc ht hg hv
  refine ⟨ha'.trans hprod',hc'.trans hprod',ht'.trans hprod',?_,?_,hv'.trans hprod'⟩
  · exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans (hg'.trans hprod')
  · exact (primeProductNorm_mono p hp hx.2.1).trans (hg'.trans hprod')


include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalSupported_divisor_bound (ell B M : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.firstDivisor ≤ (ell*Real.exp M)*B^2 := by
  have hC := (globalSupported_small_norms p hp ell M hell side x hx hs).2.1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  calc
    _ ≤ primeProductNorm p (x.common∪x.cube.support) := primeProductNorm_mono p hp hx.2.2.2
    _ = primeProductNorm p x.common*primeProductNorm p x.cube.support :=
      primeProductNorm_union p _ _ hx.2.2.1
    _ ≤ _ := mul_le_mul hC hrad (primeProductNorm_pos p hp _).le (by positivity)


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

theorem secondTailCutoff_norm_sq_le (L Y H : ℝ) (hL : 0 ≤ L) (hY : 0 < Y) (hH : 0 ≤ H)
    (k : O) (hk : k ∈ secondTailCutoff L Y H) : ‖ringComplex k‖ ^ 2 ≤ H * L ^ 3 / Y := by
  have hm : ‖ringComplex k‖ ≤ Real.sqrt (H * L ^ 3 / Y) := by
    simpa only [secondTailCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hk
  have hb := pow_le_pow_left₀ (norm_nonneg _) hm 2
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg hH (pow_nonneg hL _)) hY.le)] at hb
  exact hb

def globalNormCaps (ell B Y M H : ℝ) : Fin 10 → ℝ :=
  let L := ell * Real.exp M
  fun i => if i = 8 then H*L^2*B^2*(1+L)^3/Y
    else ![L,L,L,L,B^2,L*B^2,L,L,0,B^2] i

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def globalFirstConcreteCutoff (K ell B F M H : ℝ) (side : Bool) (b : GlobalFirstData ι) :
    Finset ι → Finset ι → Finset O :=
  fun _ _ => secondTailCutoff (globalFirstTailLength p ell M side b)
    (globalFirstPooledRow p K ell B F side b) H

include hp in
/-- The concrete lattice cutoff gives a polynomial upper bound for every descendant row. -/
theorem globalSupported_cutoff_row_bound (ell B Y M H : ℝ)
    (hell : 0 < ell) (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ secondTailCutoff (globalFirstTailLength p ell M side x.first) Y H) :
    ‖ringComplex (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤
      H * (ell * Real.exp M)^2 * B^2 * (1 + ell * Real.exp M)^3 / Y := by
  let L := ell * Real.exp M
  have hL : 0 < L := mul_pos hell (Real.exp_pos M)
  have hsmall := globalSupported_small_norms p hp ell M hell side x hx hs
  have hD := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have hX : globalFirstColumnScale p ell x side ≤ ell :=
    div_le_self hell.le (one_le_mul_of_one_le_of_one_le
      (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))
  have ht : globalFirstTailLength p ell M side x.first ≤ 1 + L := by
    change 1 + globalFirstColumnScale p ell x side * Real.exp M ≤ 1 + L
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right hX (Real.exp_pos M).le
  have htpos : 0 < globalFirstTailLength p ell M side x.first := by
    change 0 < 1 + globalFirstColumnScale p ell x side * Real.exp M
    have hh := globalFirstColumnScale_pos p hp ell hell x side
    positivity
  have hf := secondTailCutoff_norm_sq_le _ Y H htpos.le hY hH x.source.frequency hk
  have hf' : ‖ringComplex x.source.frequency‖^2 ≤ H * (1 + L)^3 / Y :=
    hf.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le ht 3) hH) hY.le)
  unfold globalSecondTuple
  rw [actualSecondTuple_newRow]
  simp only [actualSecondRow, map_mul, norm_mul, mul_pow]
  change primeProductNorm p x.firstDivisor * primeProductNorm p x.source.divisor *
    ‖ringComplex x.source.frequency‖^2 ≤ _
  calc
    _ ≤ (L * B^2) * L * (H * (1+L)^3 / Y) :=
      mul_le_mul (mul_le_mul hD hsmall.2.2.2.2.1 (primeProductNorm_pos p hp _).le
        (mul_nonneg hL.le (sq_nonneg B))) hf' (sq_nonneg _) (by positivity)
    _ = _ := by dsimp only [L]; ring

include hp in
theorem globalScaleVector_le_caps (ell B Y M H : ℝ)
    (hell : 0 < ell) (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ secondTailCutoff (globalFirstTailLength p ell M side x.first) Y H) :
    ∀ i, globalScaleVector p side x i ≤ globalNormCaps ell B Y M H i := by
  obtain ⟨ha,hc,ht,hr,he,hv⟩ := globalSupported_small_norms p hp ell M hell side x hx hs
  have hd := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have hrow := globalSupported_cutoff_row_bound p hp ell B Y M H hell hB hY hH side x hx hs hb₁ hb₂ hk
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB hb₁ hb₂).1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  have hactive : (globalCubeActiveRoot p x)^2 ≤ B^2 :=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hrad
  intro i
  fin_cases i
  · exact ha
  · exact hc
  · exact ht
  · exact hr
  · exact hJ
  · exact hd
  · exact he
  · exact hv
  · exact hrow
  · exact hactive

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

def globalRowScaleFloor (K ell B F M : ℝ) : ℝ :=
  ell^2*B^2*F^2/(K*(ell*Real.exp M)^2)

theorem globalRowScaleFloor_pos (K ell B F M : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) : 0 < globalRowScaleFloor K ell B F M := by
  unfold globalRowScaleFloor
  positivity

theorem globalNormCaps_antitone_row (ell B Y₀ Y₁ M H : ℝ) (hell : 0 < ell)
    (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y₁) (hH : 0 ≤ H) :
    ∀ i, globalNormCaps ell B Y₁ M H i ≤ globalNormCaps ell B Y₀ M H i := by
  intro i
  by_cases hi : i = 8
  · simp only [globalNormCaps, if_pos hi]
    exact div_le_div_of_nonneg_left (by positivity) hY₀ hY
  · simp only [globalNormCaps, if_neg hi, le_refl]

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
theorem globalPooled_J_bound (B : ℝ) (hB : 0 ≤ B) (side : Bool)
    (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalLogRep (globalScaleIndex p side x) 4 ≤ B^2 := by
  have hb := (globalScaleIndex_bounds p hp side x hk 4).1
  change globalLogRep (globalScaleIndex p side x) 4 ≤ globalCubeJNorm p x at hb
  exact hb.trans (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB hb₁ hb₂).1

include hp in
theorem globalRowScaleFloor_le_pooled (K ell B F M : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (side : Bool) (x : GlobalSecondData ι)
    (hx : GlobalSecondAdmissible x) (hk : x.source.frequency ≠ 0)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalRowScaleFloor K ell B F M ≤ globalPooledRowScale K ell B F (globalScaleIndex p side x) := by
  let j := globalScaleIndex p side x
  have hC : globalLogRep j 1 ≤ ell*Real.exp M :=
    (globalScaleIndex_bounds p hp side x hk 1).1.trans (globalSupported_small_norms p hp ell M hell side x hx hs).2.1
  have hJ := globalPooled_J_bound p hp B hB.le side x hk hb₁ hb₂
  have hcpos := globalLogRep_pos j 1
  have hjpos := globalLogRep_pos j 4
  have hd := globalLogRep_ge_one j 5
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  unfold globalRowScaleFloor globalPooledRowScale
  calc
    ell^2*B^2*F^2/(K*(ell*Real.exp M)^2) = ell^2*B^4*F^2/(K*(ell*Real.exp M)^2*B^2) := by field_simp
    _ ≤ Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4) := by
      apply div_le_div₀ (by positivity)
      · calc
          ell^2*B^4*F^2 = 1*ell^2*B^4*F^2*1 := by ring
          _ ≤ _ := by gcongr
      · positivity
      · gcongr

include hp in
theorem globalScaleIndex_mem_uniform_box (K ell B F M H : ℝ)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) (hH : 0 ≤ H)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk0 : x.source.frequency ≠ 0)
    (hk : x.source.frequency ∈ secondTailCutoff (globalFirstTailLength p ell M side x.first)
      (globalPooledRowScale K ell B F (globalScaleIndex p side x)) H) :
    globalScaleIndex p side x ∈ globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalScaleIndex p side x)
  have hfloor := globalRowScaleFloor_pos K ell B F M hK hell hB hF
  have hlower := globalRowScaleFloor_le_pooled p hp K ell B F M hK hell hB hF side x hx hk0 hs hb₁ hb₂
  have hcaps := globalScaleVector_le_caps p hp ell B _ M H hell hB.le hY hH side x hx hs hb₁ hb₂ hk
  apply globalScaleIndex_mem_box p hp side x hk0
  intro i
  exact (hcaps i).trans (globalNormCaps_antitone_row ell B _ _ M H hell hfloor hlower hH i)

include hp in
theorem globalFirstSupportedPool_index_mem_box
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (hs : ∀ b ∈ s, GlobalFirstAdmissible b)
    (K ell B F M H : ℝ) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) (hH : 0 ≤ H)
    (side : Bool)
    (hb₁ : ∀ b ∈ s, ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ b ∈ s, ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2 ≤ B)
    (x : GlobalSecondData ι)
    (hx : x ∈ globalFirstSupportedPool p pool s
      (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side) :
    globalScaleIndex p side x ∈ globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hm := (mem_globalFirstExpansionPool pool s _ x).mp (Finset.mem_filter.mp hx).1
  have hk := Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2
  apply globalScaleIndex_mem_uniform_box p hp K ell B F M H hK hell hB hF hH side x
    (globalFirstSupportedPool_admissible p pool s hs _ ell M side x hx)
    (Finset.mem_filter.mp hx).2 (hb₁ x.first hm.1) (hb₂ x.first hm.1) hk.1
  simpa only [globalFirstConcreteCutoff, globalPooledRowScale_first] using hk.2

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

theorem globalPooledDelta_pos (B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    0 < globalPooledDelta B F j := by
  unfold globalPooledDelta
  exact mul_pos (mul_pos (mul_pos (mul_pos hB hF) (globalLogRep_pos j 0))
    (globalLogRep_pos j 2)) (globalLogRep_pos j 3)

def globalBinTripleRange (B : ℝ) (j : GlobalLogIndex) : ℝ :=
  (B*Real.sqrt (globalLogRep j 9)/globalLogRep j 4)*globalLogRep j 2*globalLogRep j 3

def globalBinChildCharge (B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  (diagonalControl sieveCutoff)^3*(Real.exp 1)^14*globalPooledDelta B F j*B^2/globalLogRep j 4

theorem globalBinTripleRange_nonneg (B : ℝ) (hB : 0 ≤ B) (j : GlobalLogIndex) :
    0 ≤ globalBinTripleRange B j := by
  unfold globalBinTripleRange
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  have h4 := (globalLogRep_pos j 4).le
  positivity

theorem globalBin_complete_cost (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) (ray : QuadraticRayRing × QuadraticRayRing) :
    globalBinFirstCoefficient K ell B F j *
      globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
      (globalPooledColumnScale ell j*globalPooledLabelScale j) *
      ((diagonalControl sieveCutoff)^3*(Real.exp 1)^3*globalBinTripleRange B j) =
    globalBinChildCharge B F j*‖rayQuadraticPair ray.1 ray.2‖ := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  have hs := (Real.sqrt_pos.mpr (globalLogRep_pos j 9)).ne'
  have he : Real.exp 4=(Real.exp 1)^4 := by simp
  unfold globalBinFirstCoefficient globalPooledOuterBound globalPooledRowScale
    globalPooledColumnScale globalPooledLabelScale globalBinTripleRange globalBinChildCharge globalPooledDelta
  rw [he]
  field_simp [h]

theorem globalBin_mass_balance (ell B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalBinChildCharge B F j*(globalPooledColumnScale ell j*globalPooledLabelScale j) =
      (diagonalControl sieveCutoff)^3*(Real.exp 1)^18*((ell*B^3)*F) := by
  rw [globalPooled_mass ell B F hB hF]
  have hD := (globalPooledDelta_pos B F hB hF j).ne'
  have hJ := (globalLogRep_pos j 4).ne'
  have he : Real.exp 4=(Real.exp 1)^4 := by simp
  unfold globalBinChildCharge
  rw [he]
  field_simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalBin_active_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    Real.sqrt (globalLogRep (globalScaleIndex p side x) 9) ≤ globalCubeActiveRoot p x ∧
    globalCubeActiveRoot p x ≤ Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1 := by
  have hr := globalScaleIndex_bounds p hp side x hk 9
  change globalLogRep (globalScaleIndex p side x) 9 ≤ (globalCubeActiveRoot p x)^2 ∧
    (globalCubeActiveRoot p x)^2 ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 at hr
  have hx := (globalCubeActiveRoot_pos p hp x).le
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨hx,hr.1⟩
  · have hs := Real.sq_sqrt (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hrep := (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have hm : (globalCubeActiveRoot p x)^2 ≤
        (Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1)^2 := by
      calc
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 := hr.2
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*(Real.exp 1)^2 := by gcongr; nlinarith
        _ = _ := by rw [mul_pow,hs]
    exact (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos 1).le)).mp hm

include hp in
theorem globalBin_first_coefficient_bound (K ell B F : ℝ) (hK : 0 ≤ K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    K/(primeProductNorm p x.firstDivisor*ell*B^2*F*globalCubeActiveRoot p x) ≤
      globalBinFirstCoefficient K ell B F (globalScaleIndex p side x) := by
  have hd := (globalScaleIndex_bounds p hp side x hk 5).1
  have ha := (globalBin_active_bounds p hp side x hk).1
  change globalLogRep (globalScaleIndex p side x) 5 ≤ primeProductNorm p x.firstDivisor at hd
  have h5 := globalLogRep_pos (globalScaleIndex p side x) 5
  have hs := Real.sqrt_pos.mpr (globalLogRep_pos (globalScaleIndex p side x) 9)
  have hd0 := (primeProductNorm_pos p hp x.firstDivisor).le
  unfold globalBinFirstCoefficient
  apply div_le_div_of_nonneg_left hK (by positivity)
  gcongr

include hp in
theorem globalBin_triple_bounds (B : ℝ) (hB : 0 < B) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4 ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ globalLogRep j 2*Real.exp 1 ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ globalLogRep j 3*Real.exp 1 := by
  dsimp only
  exact globalSecondFixedTriple_norm_bounds p hp x B _ _ _ _ hB.le (globalLogRep_pos _ 4)
    hb₁ hb₂ (globalBin_active_bounds p hp side x hk).2
    (globalScaleIndex_bounds p hp side x hk 4).1
    (globalScaleIndex_bounds p hp side x hk 2).2 (globalScaleIndex_bounds p hp side x hk 3).2

include hp in

theorem globalBin_triple_count (B : ℝ) (hB : 0 < B) (side : Bool)
    (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hj : ∀ x∈s,globalScaleIndex p side x=j)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤
      (diagonalControl sieveCutoff)^3*(Real.exp 1)^3*globalBinTripleRange B j := by
  have hcontrol := diagonalControl_nonneg sieveCutoff
  by_cases hs : s.Nonempty
  · obtain ⟨x,hxs⟩ := hs
    have hb := globalBin_triple_bounds p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
    dsimp only at hb
    rw [hj x hxs] at hb
    have hn : 1 ≤ (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) := by
      have hh : 1 ≤ Ideal.absNorm (globalSecondFixedTriple p x).1 :=
        Nat.one_le_iff_ne_zero.mpr (fun h => (globalSecondFixedTriple_nonzero p hp x).1 (Ideal.absNorm_eq_zero_iff.mp h))
      exact_mod_cast hh
    have hcount := globalSecondFixedTriple_count p hp s B
      (Real.sqrt (globalLogRep j 9)*Real.exp 1) (globalLogRep j 4)
      (globalLogRep j 2*Real.exp 1) (globalLogRep j 3*Real.exp 1)
      hB.le (globalLogRep_pos j 4) (hn.trans hb.1)
      (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 2) (Real.one_le_exp (by norm_num)))
      (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 3) (Real.one_le_exp (by norm_num))) hb₁ hb₂
      (fun y hy => by have hh := (globalBin_active_bounds p hp side y (hk y hy)).2; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 4).1; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 2).2; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 3).2; rwa [hj y hy] at hh)
    convert hcount using 1 ; unfold globalBinTripleRange ; ring
  · have hz : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hz]
    simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (by positivity) (globalBinTripleRange_nonneg B hB.le j)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def globalBinTriples (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) :
    Finset (Ideal O × Ideal O × Ideal O) :=
  (globalLogSector p s side j).image (globalSecondFixedTriple p)

theorem sum_globalArithmeticBin {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (f : GlobalSecondData ι → M) :
    ∑ x ∈ globalLogSector p s side j, f x =
      ∑ q ∈ globalBinTriples p s side j, ∑ x ∈ globalArithmeticBin p s side q j, f x := by
  have h := sum_globalSecondFixedTriple p (globalLogSector p s side j) f
  simpa only [globalBinTriples, globalLogSector, globalArithmeticBin, Finset.filter_filter, and_comm] using h

theorem sum_globalLogSector_of_mem {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (I : Finset GlobalLogIndex)
    (hI : ∀ x ∈ s, globalScaleIndex p side x ∈ I) (f : GlobalSecondData ι → M) :
    ∑ x ∈ s, f x = ∑ j ∈ I, ∑ x ∈ globalLogSector p s side j, f x :=
  (Finset.sum_fiberwise_of_maps_to hI f).symm

theorem globalBinTriples_nonzero (hp : ∀ i, p i ≠ 0)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (q : Ideal O × Ideal O × Ideal O) (hq : q ∈ globalBinTriples p s side j) : q.1 ≠ ⊥ := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  exact (globalSecondFixedTriple_nonzero p hp x).1

theorem globalBinTriples_count (hp : ∀ i, p i ≠ 0)
    (B : ℝ) (hB : 0 < B) (side : Bool) (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x ∈ s, x.source.frequency ≠ 0)
    (hb₁ : ∀ x ∈ s, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x ∈ s, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ((globalBinTriples p s side j).card : ℝ) ≤
      (diagonalControl sieveCutoff)^3 * (Real.exp 1)^3 * globalBinTripleRange B j :=
  globalBin_triple_count p hp B hB side (globalLogSector p s side j) j
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx => hk x (Finset.mem_filter.mp hx).1)
    (fun x hx => hb₁ x (Finset.mem_filter.mp hx).1)
    (fun x hx => hb₂ x (Finset.mem_filter.mp hx).1)

theorem globalBinTriples_label_bound (hp : ∀ i, p i ≠ 0)
    (B : ℝ) (hB : 0 < B) (side : Bool) (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x ∈ s, x.source.frequency ≠ 0)
    (hb₁ : ∀ x ∈ s, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x ∈ s, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (q : Ideal O × Ideal O × Ideal O) (hq : q ∈ globalBinTriples p s side j) :
    (Ideal.absNorm q.1 : ℝ) ≤ B * (Real.sqrt (globalLogRep j 9) * Real.exp 1) / globalLogRep j 4 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hxs,hxj⟩ := Finset.mem_filter.mp hx
  have hh := (globalBin_triple_bounds p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)).1
  rwa [hxj] at hh

variable (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem globalSecondFixedLiteralTerm_pooled_row
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ))
    (K ell B F : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : GlobalSecondData ι)
    (j : GlobalLogIndex) (hxj : globalScaleIndex p side x = j) :
    globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t
      (globalFirstPooledRow p K ell B F side) ray s q x =
    globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t
      (fun _ => globalPooledRowScale K ell B F j) ray s q x := by
  unfold globalSecondFixedLiteralTerm
  rw [← globalPooledRowScale_first p K ell B F side x, hxj]

/-- Within a logarithmic bin the first coefficient and row scale are constant. -/
theorem globalLiteral_bin_first_coefficient
    (source : Finset (GlobalSecondData ι)) (w : GlobalFirstData ι → ℂ)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ))
    (K ell B F : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (q₀ : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) :
    (∑ x ∈ globalArithmeticBin p source side q₀ j,
      (w x.first * (globalFirstCoefficient p K ell B F side x.first : ℂ)) *
        globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t
          (globalFirstPooledRow p K ell B F side) ray s q x) =
      (globalBinFirstCoefficient K ell B F j : ℂ) *
        ∑ x ∈ globalArithmeticBin p source side q₀ j,
          w x.first * globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t
            (fun _ => globalPooledRowScale K ell B F j) ray s q x := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxj := (Finset.mem_filter.mp hx).2.2
  have hc := globalBinFirstCoefficient_first p K ell B F side x
  rw [hxj] at hc
  rw [← hc, globalSecondFixedLiteralTerm_pooled_row p hg pool Ψ m g V W K ell B F side r t ray s q x j hxj]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap ContDiff
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The finite descendant energy retains radial decay and all fixed arithmetic residue columns. -/
def globalChildBudget (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε K ell B F : ℝ) (I : Finset GlobalLogIndex) (A J : ℕ) (side : Bool) : ℝ :=
  ∑ ray : QuadraticRayRing × QuadraticRayRing,
    ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
      ∑ j ∈ I, ∑ q₀ ∈ globalBinTriples p source side j,
        (C * globalBinFirstCoefficient K ell B F j *
          globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
          (globalPooledLabelScale j * Ideal.absNorm q₀.1)^ε /
          (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A) *
        densityChildEnergy p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
          pool Ψ Ψ (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j)
          (windows 5) (windows 6) (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J

/-- The complete nonzero source is bounded by a finite sum of fixed descendant energies. -/
theorem full_uniform_globalFirstTruncatedSource_bound
    (g V W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (side : Bool) (ε : ℝ) (hε : 0 < ε) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      (∀ i u, windows i u ≠ 0 → |u| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda^2 ∣ p i - 1)
        (pool : Finset ι) (s₀ : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
        (Ψ : O →* ℂ) (m : O) (Γ K ell B F t : ℝ) (r : QuadraticRayRing)
        (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (I : Finset GlobalLogIndex),
      0 ≤ Γ → (∀ b ∈ s₀, ‖w b‖ ≤ Γ) → 0 < K → 0 < ell → 0 < B → 0 < F →
      (∀ a, ‖Ψ a‖ ≤ 1) → (∀ b ∈ s₀, GlobalFirstAdmissible b) →
      let source := globalFirstSupportedPool p pool s₀ (fun b G E => (cutoff b G E).erase 0) ell M side
      (∀ x ∈ source, globalScaleIndex p side x ∈ I) →
      ‖globalFirstTruncatedSource p hp hg pool s₀
        (fun b => w b * (globalFirstCoefficient p K ell B F side b : ℂ)) Ψ m g V W ell side r t
        (globalFirstPooledRow p K ell B F side) (fun b G E => (cutoff b G E).erase 0)‖ ≤
        (1+‖t‖)^(2*(J+2)) *
          globalChildBudget p hg pool source Ψ m windows (Γ*C) ε K ell B F I A J side := by
  obtain ⟨windows,C,hC,hwc,hws,hwb,hbin⟩ := full_uniform_globalLiteral_bin_bound g V W M hM hgM side ε hε A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg hinj hc hpr pool s₀ w Ψ m Γ K ell B F t r cutoff I
    hΓ hw hK hell hB hF hΨ hs
  dsimp only
  intro hI
  let source := globalFirstSupportedPool p pool s₀ (fun b G E => (cutoff b G E).erase 0) ell M side
  have hsource (x : GlobalSecondData ι) (hx : x ∈ source) : GlobalSecondAdmissible x :=
    globalFirstSupportedPool_admissible p pool s₀ hs _ ell M side x hx
  have hk (x : GlobalSecondData ι) (hx : x ∈ source) : x.source.frequency ≠ 0 :=
    globalFirstSupportedPool_frequency_ne_zero p pool s₀ cutoff ell M side x hx
  have hweight (x : GlobalSecondData ι) (hx : x ∈ source) : ‖w x.first‖ ≤ Γ :=
    hw x.first ((mem_globalFirstExpansionPool pool s₀ _ x).mp (Finset.mem_filter.mp hx).1).1
  rw [globalFirstTruncatedSource_eq_supported_fixed p hp hg hinj hc hpr pool s₀ _ Ψ m g V W
    ell M hell hgM side r t]
  simp only [globalChildBudget, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ray _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [sum_globalLogSector_of_mem p source side I hI]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [sum_globalArithmeticBin p source side j]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q₀ hq₀
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hcoef := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hr := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell hY j
  have hpow : 0 < (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A :=
    pow_pos (by linarith only [hr]) A
  have hb := hbin p hp hg hinj hpr source (fun x => w x.first) Γ q₀ j pool Ψ m r ray s q
    ell (globalPooledRowScale K ell B F j) t hΓ hweight hell hY
    (globalBinTriples_nonzero p hp source side j q₀ hq₀) hΨ hsource hk
  rw [mul_comm ((1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A)] at hb
  have hn := (le_div_iff₀ hpow).mpr hb
  rw [globalLiteral_bin_first_coefficient p hg source w pool Ψ m g V W K ell B F side r t ray s q q₀ j,
    norm_mul, Complex.norm_of_nonneg hcoef]
  exact (mul_le_mul_of_nonneg_left hn hcoef).trans_eq (by ring)

end SecondPassArithmetic

namespace FirstPassCubeLabels
open scoped BigOperators
open MeasureTheory SecondPassArithmetic

lemma firstLogDensity_pair_moment (J : ℕ) (t : ℝ) :
    firstLogDensity (2*(J+2)) t * ((1+‖t‖)^(J+2) * (1+‖t‖)^(J+2)) = firstLogDensity 0 t := by
  rw [← pow_add, show J+2+(J+2)=2*(J+2) by omega]
  exact JointLogSeparation.density_weight_identity _ _

lemma firstLogDensity_le_zero (J : ℕ) (t : ℝ) : firstLogDensity J t ≤ firstLogDensity 0 t := by
  have h := pow_le_pow_right₀ (show 1 ≤ 1+‖t‖ by linarith [norm_nonneg t]) (show 2 ≤ J+2 by omega)
  apply inv_anti₀ (by positivity : 0 < (1+‖t‖)^2) h

lemma integral_pair_moment_bound (J : ℕ) (f : ℝ → ℝ)
    (hf : Integrable (fun t => firstLogDensity (2*(J+2)) t * f t))
    (a d c q : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (h : ∀ t, f t ≤ a*(d + ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c + q)) :
    (∫ t, firstLogDensity (2*(J+2)) t * f t) ≤
      (∫ t, firstLogDensity 0 t) * a * (d+c+q) := by
  have hi := (firstLogDensity_integrable 0).mul_const (a*(d+c+q))
  have hm : ∀ t, firstLogDensity (2*(J+2)) t * f t ≤ firstLogDensity 0 t*(a*(d+c+q)) := by
    intro t
    apply (mul_le_mul_of_nonneg_left (h t) (firstLogDensity_nonneg _ _)).trans
    have h1 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hd)
    have h2 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hq)
    have he := firstLogDensity_pair_moment J t
    calc
      _ = firstLogDensity (2*(J+2)) t*(a*d) +
          (firstLogDensity (2*(J+2)) t*((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2)))*(a*c) +
          firstLogDensity (2*(J+2)) t*(a*q) := by ring
      _ ≤ firstLogDensity 0 t*(a*d) + firstLogDensity 0 t*(a*c) + firstLogDensity 0 t*(a*q) := by
        rw [he]
        exact add_le_add (add_le_add h1 le_rfl) h2
      _ = _ := by ring
  have hh := integral_mono hf hi hm
  rw [integral_mul_const] at hh
  simpa only [mul_assoc] using hh

end FirstPassCubeLabels

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
