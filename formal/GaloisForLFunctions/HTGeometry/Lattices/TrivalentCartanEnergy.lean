import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ExceptionalChainBoundaryEnergy
import GaloisForLFunctions.HTGeometry.TriangleSignatureTrichotomy
import Mathlib.NumberTheory.ADEInequality

/-!
# The trivalent Cartan form and its affine boundary

An arm with n interior vertices has effective conductance 1/(n+1).
Gluing three arms at a vertex of diagonal weight two subtracts one
central square from their combined Dirichlet energy. Eliminating the
arms identifies all finite types and the nullspace at the affine boundary.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.TrivalentCartan
open SignedArithmeticEnergyIncidence

/-- Extend an arm by its central vertex. -/
def extend {n : ℕ} (t : ℝ) (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then f ⟨k,h⟩ else t

private theorem terminal {n : ℕ} (t : ℝ) (f : Fin n → ℝ) : extend t f n = t := by simp [extend]

/-- Arm coordinates run from the outside towards the common vertex. -/
def arm {n : ℕ} (t : ℝ) (f : Fin n → ℝ) :=
  exceptionalChainEnergy n (extend t f)-((n:ℝ)+2)*t^2

def ramp (n : ℕ) (t : ℝ) (i : Fin n) := exceptionalChainRamp n t i

private def conductance (n : ℕ) := 1/((n:ℝ)+1)

private theorem arm_minimum {n : ℕ} (t : ℝ) (f : Fin n → ℝ) :
    conductance n*t^2 ≤ arm t f ∧ (arm t f=conductance n*t^2 ↔ f=ramp n t) := by
  have h := exceptionalChainEnergy_boundary_bound n (extend t f)
  have he := exceptionalChainEnergy_minimizers n (extend t f)
  rw [terminal] at h he
  unfold arm conductance
  refine ⟨by linarith only [h],?_⟩
  constructor
  · intro hv
    have hh := he.mp (by linarith only [hv])
    funext i
    simpa only [extend,dif_pos i.isLt,ramp] using hh i i.isLt.le
  · rintro rfl
    have h' : ∀ k ≤ n, extend t (ramp n t) k=exceptionalChainRamp n t k := by
      intro k hk
      rcases lt_or_eq_of_le hk with hk | heq
      · simp [extend,hk,ramp]
      · subst k
        rw [terminal,exceptionalChainRamp,mul_div_cancel_left₀ _ (by positivity : (n:ℝ)+1 ≠ 0)]
    linarith only [he.mpr h']

/-- The Cartan energy in vertex coordinates. Each vertex contributes twice
its square, and each edge contributes minus twice its endpoint product. -/
def energy {n m k : ℕ} (t : ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) (h : Fin k → ℝ) :=
  arm t f+arm t g+arm t h-t^2

/-- Actual edge expansion on a single arm, with the center counted once. -/
theorem arm_edges {n : ℕ} (t : ℝ) (f : Fin n → ℝ) :
    arm t f = 2*(∑ i ∈ range n, (extend t f i)^2)+t^2 -
      2*∑ i ∈ range n, extend t f i*extend t f (i+1) := by
  rw [arm,exceptionalChainEnergy_expansion,sum_range_succ,terminal]
  ring

/-- The residual coefficient after eliminating all interior vertices. -/
def center (n m k : ℕ) := conductance n+conductance m+conductance k-1

/-- The sharp lower bound at prescribed center, including all minimizers. -/
theorem center_minimum {n m k : ℕ} (t : ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) (h : Fin k → ℝ) :
    center n m k*t^2 ≤ energy t f g h ∧
      (energy t f g h=center n m k*t^2 ↔ f=ramp n t ∧ g=ramp m t ∧ h=ramp k t) := by
  obtain ⟨hf,ef⟩ := arm_minimum t f
  obtain ⟨hg,eg⟩ := arm_minimum t g
  obtain ⟨hh,eh⟩ := arm_minimum t h
  unfold center energy
  refine ⟨by linarith only [hf,hg,hh],?_⟩
  rw [← ef,← eg,← eh]
  constructor
  · intro hs
    exact ⟨by linarith only [hs,hf,hg,hh],by linarith only [hs,hf,hg,hh],by linarith only [hs,hf,hg,hh]⟩
  · rintro ⟨a,b,c⟩
    rw [a,b,c]
    ring

private theorem attains (n m k : ℕ) (t : ℝ) :
    energy t (ramp n t) (ramp m t) (ramp k t) = center n m k*t^2 :=
  (center_minimum _ _ _ _).2.mpr ⟨rfl,rfl,rfl⟩

/-- Positive definiteness on the full vertex space. Zero-length arms are allowed. -/
def positive (n m k : ℕ) :=
  ∀ (t : ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) (h : Fin k → ℝ),
    (t ≠ 0 ∨ f ≠ 0 ∨ g ≠ 0 ∨ h ≠ 0) → 0 < energy t f g h

private theorem ramp_zero (n : ℕ) : ramp n 0=0 := by
  funext i
  simp [ramp,exceptionalChainRamp]

theorem positive_iff (n m k : ℕ) : positive n m k ↔ 0 < center n m k := by
  constructor
  · intro hp
    have he := hp 1 (ramp n 1) (ramp m 1) (ramp k 1) (Or.inl one_ne_zero)
    simpa only [attains,one_pow,mul_one] using he
  · intro hs t f g h nonzero
    have he := center_minimum t f g h
    by_cases ht : t=0
    · subst t
      simp only [zero_pow (by decide : 2≠0),mul_zero,ramp_zero] at he
      apply lt_of_le_of_ne he.1
      intro eq
      obtain ⟨rfl,rfl,rfl⟩ := he.2.mp eq.symm
      simp at nonzero
    · exact (mul_pos hs (sq_pos_of_ne_zero ht)).trans_le he.1

/-- Edge count from the pinned exterior point to the center. -/
def lengthPNat (n : ℕ) : ℕ+ := ⟨n+1,Nat.succ_pos _⟩

private def reciprocalSum (n m k : ℕ) : ℚ :=
  1/((n+1:ℕ):ℚ)+1/((m+1:ℕ):ℚ)+1/((k+1:ℕ):ℚ)

private theorem center_eq (n m k : ℕ) : center n m k = ((reciprocalSum n m k : ℚ):ℝ)-1 := by
  unfold center conductance reciprocalSum
  push_cast
  rfl

/-- An actual trivalent Cartan form is positive definite exactly for the A,
D and E arm triples, up to permutations. -/
theorem finite_type_classification (n m k : ℕ) :
    positive n m k ↔ ADEInequality.Admissible {lengthPNat n,lengthPNat m,lengthPNat k} := by
  rw [positive_iff,center_eq,sub_pos,← ADEInequality.classification,ADEInequality.sumInv_pqr]
  simp only [← one_div]
  change (1:ℝ) < (reciprocalSum n m k : ℝ) ↔ (1:ℚ) < reciprocalSum n m k
  constructor <;> intro h <;> exact_mod_cast h

/-- Semidefiniteness and the nullspace for every affine arm triple. -/
theorem affine_nullspace (n m k : ℕ) :
    center n m k = 0 →
      ∀ t (f : Fin n → ℝ) (g : Fin m → ℝ) (h : Fin k → ℝ),
        0 ≤ energy t f g h ∧ (energy t f g h=0 ↔ f=ramp n t ∧ g=ramp m t ∧ h=ramp k t) := by
  intro hs t f g h
  simpa only [hs,zero_mul] using center_minimum t f g h

/-- All indefinite trivalent forms have a common explicit negative direction. -/
theorem negative_direction (n m k : ℕ) :
    (∃ (t : ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) (h : Fin k → ℝ), energy t f g h < 0) ↔
      center n m k < 0 := by
  constructor
  · rintro ⟨t,f,g,h,ht⟩
    by_contra! hs
    exact ht.not_ge ((mul_nonneg hs (sq_nonneg t)).trans (center_minimum t f g h).1)
  · intro hs
    exact ⟨1,ramp n 1,ramp m 1,ramp k 1,by simpa only [attains,one_pow,mul_one] using hs⟩

/-- The zero mode occurs at exactly three ordered arm triples. Here the
lengths count vertices strictly outside the center. -/
theorem affine_shape (n m k : ℕ) (hn : 0 < n) (hm : n ≤ m) (hk : m ≤ k) :
    center n m k=0 ↔ (n=1 ∧ m=2 ∧ k=5) ∨ (n=1 ∧ m=3 ∧ k=3) ∨ (n=2 ∧ m=2 ∧ k=2) := by
  constructor
  · intro h
    rw [center_eq,sub_eq_zero] at h
    have hh : reciprocalSum n m k=1 := by exact_mod_cast h
    have hshape := euclidean_cone_triple (a:=n+1) (b:=m+1) (c:=k+1)
      (by omega) (by omega) (by omega) hh
    omega
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩) <;> norm_num [center,conductance]

/-- Indefinite forms have a uniform gap at center one. For ordered arms
equality singles out the hyperbolic extension of the E₈ diagram. -/
theorem indefinite_gap (n m k : ℕ) :
    center n m k < 0 → center n m k ≤ -1/42 ∧
      (n ≤ m → m ≤ k → (center n m k= -1/42 ↔ n=1 ∧ m=2 ∧ k=6)) := by
  rw [center_eq]
  intro h
  have hr : reciprocalSum n m k < 1 := by
    exact_mod_cast (show ((reciprocalSum n m k : ℚ):ℝ) < 1 by linarith only [h])
  have hub : reciprocalSum n m k ≤ 41/42 := hurwitz_triple_sum_le_symm (p:=n+1) (q:=m+1)
    (r:=k+1) (by omega) (by omega) (by omega) hr
  let q : ℚ := 41/42
  have cast_q : (q:ℝ) = 41/42 := by norm_num [q]
  have hh : (reciprocalSum n m k : ℝ) ≤ (q:ℝ) := by exact_mod_cast (show reciprocalSum n m k ≤ q from hub)
  rw [cast_q] at hh
  refine ⟨by linarith only [hh],fun hm hk => ?_⟩
  constructor
  · intro he
    have he' : reciprocalSum n m k=41/42 := by
      change reciprocalSum n m k = q
      exact_mod_cast (show (reciprocalSum n m k : ℝ) = (q:ℝ) by rw [cast_q]; linarith only [he])
    have hs := hurwitz_ordered_eq_237 (p:=n+1) (q:=m+1) (r:=k+1)
      (by omega) (by omega) (by omega) hr he'
    omega
  · rintro ⟨rfl,rfl,rfl⟩
    norm_num [reciprocalSum]

/-- Integer directions suffice to test the three-arm form. -/
def integerPositive (n m k : ℕ) :=
  ∀ (t : ℤ) (f : Fin n → ℤ) (g : Fin m → ℤ) (h : Fin k → ℤ),
    (t≠0 ∨ f≠0 ∨ g≠0 ∨ h≠0) →
      0 < energy (t:ℝ) (fun i => (f i:ℝ)) (fun i => (g i:ℝ)) (fun i => (h i:ℝ))

private def pin (n m k : ℕ) : ℤ := (n+1:ℤ)*(m+1:ℤ)*(k+1:ℤ)

private def integralArm (n m k : ℕ) (i : Fin n) : ℤ := ((i.val:ℤ)+1)*(m+1:ℤ)*(k+1:ℤ)

private theorem integral_arm_ramp (n m k : ℕ) :
    (fun i => (integralArm n m k i:ℝ))=ramp n (pin n m k) := by
  funext i
  unfold integralArm ramp exceptionalChainRamp pin
  push_cast
  field_simp [show (n:ℝ)+1≠0 by positivity]

/-- Multiplying the prescribed center by the product of the three arm
denominators realizes the Schur-complement minimum at an integer vector. -/
theorem integral_center_witness (n m k : ℕ) :
    ∃ (t : ℤ) (f : Fin n → ℤ) (g : Fin m → ℤ) (h : Fin k → ℤ), 0 < t ∧
      energy (t:ℝ) (fun i => (f i:ℝ)) (fun i => (g i:ℝ)) (fun i => (h i:ℝ))=
        center n m k*(t:ℝ)^2 := by
  refine ⟨pin n m k,integralArm n m k,integralArm m k n,integralArm k n m,by unfold pin; positivity,?_⟩
  have hm : pin m k n=pin n m k := by unfold pin; ring
  have hk : pin k n m=pin n m k := by unfold pin; ring
  rw [integral_arm_ramp,integral_arm_ramp,integral_arm_ramp,hm,hk,attains]

/-- The positive integral and real three-arm Cartan forms have exactly the
same arm lengths. Any failure is witnessed inside the original lattice. -/
theorem integer_positive_iff (n m k : ℕ) : integerPositive n m k ↔ positive n m k := by
  constructor
  · intro h
    obtain ⟨t,f,g,u,ht,e⟩ := integral_center_witness n m k
    have pos := h t f g u (Or.inl ht.ne')
    rw [e] at pos
    exact (positive_iff n m k).mpr ((mul_pos_iff_of_pos_right (sq_pos_of_pos (by exact_mod_cast ht : (0:ℝ) < t))).mp pos)
  · intro h t f g u nz
    apply h
    contrapose! nz
    obtain ⟨ht,hf,hg,hu⟩ := nz
    refine ⟨by exact_mod_cast ht,?_,?_,?_⟩
    · funext i
      exact_mod_cast (show (f i : ℝ) = 0 from congrFun hf i)
    · funext i
      exact_mod_cast (show (g i : ℝ) = 0 from congrFun hg i)
    · funext i
      exact_mod_cast (show (u i : ℝ) = 0 from congrFun hu i)

private theorem center_antitone {a b c n m k : ℕ} (ha : a ≤ n) (hb : b ≤ m) (hc : c ≤ k) :
    center n m k ≤ center a b c := by
  have armLe {u v : ℕ} (h : u ≤ v) : conductance v ≤ conductance u := by
    unfold conductance
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
  unfold center
  linarith only [armLe ha,armLe hb,armLe hc]

/-- Sorted nonempty arms give a fork of type D or one of the three exceptional
length triples (1,2,2), (1,2,3), (1,2,4). -/
theorem ordered_finite_shape (n m k : ℕ) (hn : 0 < n) (hm : n ≤ m) (hk : m ≤ k) :
    integerPositive n m k ↔ n=1 ∧ (m=1 ∨ (m=2 ∧ k ≤ 4)) := by
  rw [integer_positive_iff,positive_iff]
  constructor
  · intro pos
    have wall {a b c : ℕ} (ha : a ≤ n) (hb : b ≤ m) (hc : c ≤ k) (z : center a b c=0) : False := by
      have le := center_antitone ha hb hc
      rw [z] at le
      exact pos.not_ge le
    have one : n=1 := by
      by_contra ne
      exact wall (a:=2) (b:=2) (c:=2) (by omega) (by omega) (by omega) (by norm_num [center,conductance])
    refine ⟨one,?_⟩
    by_cases short : m=1
    · exact Or.inl short
    · have two : m=2 := by
        by_contra ne
        exact wall (a:=1) (b:=3) (c:=3) (by omega) (by omega) (by omega) (by norm_num [center,conductance])
      refine Or.inr ⟨two,?_⟩
      by_contra! tooLong
      exact wall (a:=1) (b:=2) (c:=5) (by omega) (by omega) (by omega) (by norm_num [center,conductance])
  · rintro ⟨rfl,h⟩
    rcases h with rfl|⟨rfl,len⟩
    · unfold center conductance
      have pos : 0 < 1/((k:ℝ)+1) := by positivity
      linarith only [pos]
    · exact lt_of_lt_of_le (by norm_num [center,conductance] : 0 < center 1 2 4)
        (center_antitone le_rfl le_rfl len)

#print axioms integral_center_witness
#print axioms integer_positive_iff
#print axioms ordered_finite_shape
#print axioms center_minimum
#print axioms finite_type_classification
#print axioms affine_nullspace
#print axioms negative_direction
#print axioms affine_shape
#print axioms indefinite_gap
end GaloisForLFunctions.HTGeometry.TrivalentCartan
