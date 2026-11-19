import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceLattice

/-!
# Sums of integral squares at trace one on the orbit cubic

The positive trace form is the ordinary sum of three squares on the
integral reciprocal basis. A sum of polynomial squares can have trace one
only when one polynomial represents a signed basis vector and all others
vanish. This leaves exactly three possible values at the roots.
-/

noncomputable section
open Finset Polynomial
namespace RHTower.OrbitCubic

/-- Evaluation of a sum of squares in the monogenic order. -/
def integralSquares {k : ℕ} (P : Fin k → ℤ[X]) (x : ℝ) : ℝ :=
  ∑ i, ((P i).eval₂ (Int.castRingHom ℝ) x)^2

private theorem single_energy {k : ℕ} (e : Fin k → ℤ)
    (he : ∀ i, 0 ≤ e i) (h : ∑ i, e i = 1) :
    ∃ i, e i = 1 ∧ ∀ j, j ≠ i → e j = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, 0 < e i := by
    by_contra! hn
    have hz := Finset.sum_eq_zero (s := (univ : Finset (Fin k)))
      (fun j _ => le_antisymm (hn j) (he j))
    omega
  have hpart := Finset.sum_erase_add (s := (univ : Finset (Fin k))) e (mem_univ i)
  have hp : 0 ≤ ∑ j ∈ univ.erase i, e j := sum_nonneg fun j _ => he j
  have hrest : ∑ j ∈ univ.erase i, e j = 0 := by omega
  refine ⟨i,by omega,fun j hj => ?_⟩
  exact (sum_eq_zero_iff_of_nonneg (fun l _ => he l)).mp hrest j
    (mem_erase.mpr ⟨hj,mem_univ _⟩)

private theorem axis_square {A B C : ℤ} (h : A^2+B^2+C^2 = 1) :
    (∀ x, (traceBasis A B C x)^2 = 1) ∨
    (∀ x, (traceBasis A B C x)^2 = x⁻¹^2) ∨
    (∀ x, (traceBasis A B C x)^2 = (x-1)⁻¹^2) := by
  have ha := sq_nonneg A
  have hb := sq_nonneg B
  have hc := sq_nonneg C
  have axis : A^2=1 ∨ B^2=1 ∨ C^2=1 := by omega
  rcases axis with hA|hB|hC
  · have hB := sq_eq_zero_iff.mp (show B^2=0 by omega)
    have hC := sq_eq_zero_iff.mp (show C^2=0 by omega)
    left
    intro x
    simpa only [traceBasis,hB,hC,Int.cast_zero,zero_mul,add_zero] using
      (show (A:ℝ)^2=1 by exact_mod_cast hA)
  · have hA := sq_eq_zero_iff.mp (show A^2=0 by omega)
    have hC := sq_eq_zero_iff.mp (show C^2=0 by omega)
    exact Or.inr (Or.inl fun x => by
      simp [traceBasis,hA,hC,mul_pow,show (B:ℝ)^2=1 by exact_mod_cast hB])
  · have hA := sq_eq_zero_iff.mp (show A^2=0 by omega)
    have hB := sq_eq_zero_iff.mp (show B^2=0 by omega)
    exact Or.inr (Or.inr fun x => by
      simp [traceBasis,hA,hB,mul_pow,show (C:ℝ)^2=1 by exact_mod_cast hC])

private theorem weighted_sum {k : ℕ} (a b c : ℝ) (f : Fin k → ℝ → ℝ) :
    weighted a b c (fun x => ∑ i, f i x) = ∑ i, weighted a b c (f i) := by
  simp only [weighted,mul_sum,sum_add_distrib]

private theorem classify_squares {m : ℤ} {a b c : ℝ}
    (ha : binary ((m:ℝ)-1/2) a 1 = 0) (hb : binary ((m:ℝ)-1/2) b 1 = 0)
    (hc : binary ((m:ℝ)-1/2) c 1 = 0)
    (ht : ∀ u v w, weighted a b c (fun x => (traceBasis u v w x)^2) = u^2+v^2+w^2)
    {k : ℕ} (P : Fin k → ℤ[X]) (h : weighted a b c (integralSquares P) = 1) :
    let agrees := fun f : ℝ → ℝ => ∀ x, binary ((m:ℝ)-1/2) x 1 = 0 → integralSquares P x = f x
    agrees (fun _ => 1) ∨ agrees (fun x => x⁻¹^2) ∨ agrees (fun x => (x-1)⁻¹^2) := by
  classical
  choose A B C hP using fun i => integral_polynomial_coordinates m (P i)
  let e := fun i => A i^2+B i^2+C i^2
  have hi (i : Fin k) :
      weighted a b c (fun x => ((P i).eval₂ (Int.castRingHom ℝ) x)^2) = (e i : ℝ) := by
    simp only [weighted,hP i a ha,hP i b hb,hP i c hc]
    simpa only [weighted,e,Int.cast_add,Int.cast_pow] using ht (A i) (B i) (C i)
  change weighted a b c (fun x => ∑ i, ((P i).eval₂ (Int.castRingHom ℝ) x)^2) = 1 at h
  rw [weighted_sum] at h
  simp only [hi,← Int.cast_sum] at h
  have hsum : ∑ i, e i = 1 := by exact_mod_cast h
  have hnon (i) : 0 ≤ e i := by dsimp [e]; positivity
  obtain ⟨i,hei,hrest⟩ := single_energy e hnon hsum
  have hs (x : ℝ) (hx : binary ((m:ℝ)-1/2) x 1 = 0) :
      integralSquares P x = (traceBasis (A i) (B i) (C i) x)^2 := by
    unfold integralSquares
    rw [Finset.sum_eq_single i, hP i x hx]
    · intro j _ hj
      have hz := hrest j hj
      dsimp [e] at hz
      have hz' (s t u : ℤ) (hh : s^2+t^2+u^2 = 0) : s = 0 := by
        apply sq_eq_zero_iff.mp
        nlinarith only [hh,sq_nonneg s,sq_nonneg t,sq_nonneg u]
      have ha' := hz' _ _ _ hz
      have hb' := hz' (B j) (C j) (A j) (by linarith only [hz])
      have hc' := hz' (C j) (A j) (B j) (by linarith only [hz])
      simp [hP j x hx,ha',hb',hc',traceBasis]
    · simp
  rcases axis_square hei with h1 | h2 | h3
  · exact Or.inl fun x hx => (hs x hx).trans (h1 x)
  · exact Or.inr (Or.inl fun x hx => (hs x hx).trans (h2 x))
  · exact Or.inr (Or.inr fun x hx => (hs x hx).trans (h3 x))

/-- At every integral parameter, the trace-one sums of squares of elements
of the monogenic order are exactly 1, the square of the inverse generator,
and the square of its inverse translate. The classification holds on all
real roots simultaneously. -/
theorem trace_one_squares_iff (m : ℤ) :
    ∃ a b c : ℝ, binary ((m:ℝ)-1/2) a 1 = 0 ∧ binary ((m:ℝ)-1/2) b 1 = 0 ∧
      binary ((m:ℝ)-1/2) c 1 = 0 ∧
      ∀ (k : ℕ) (P : Fin k → ℤ[X]),
        let agrees := fun f : ℝ → ℝ => ∀ x, binary ((m:ℝ)-1/2) x 1 = 0 → integralSquares P x = f x
        weighted a b c (integralSquares P) = 1 ↔
          agrees (fun _ => 1) ∨ agrees (fun x => x⁻¹^2) ∨ agrees (fun x => (x-1)⁻¹^2) := by
  obtain ⟨a,b,c,ha,hb,hc,_,_,_,ht⟩ := exists_orthonormal_trace_basis (m:ℝ)
  refine ⟨a,b,c,ha,hb,hc,fun k P => ⟨classify_squares ha hb hc (fun u v w => (ht u v w).2) P,?_⟩⟩
  rintro (h|h|h) <;> rw [weighted,h a ha,h b hb,h c hc]
  · simpa [weighted,traceBasis] using (ht 1 0 0).2
  · simpa [weighted,traceBasis] using (ht 0 1 0).2
  · simpa [weighted,traceBasis] using (ht 0 0 1).2

#print axioms trace_one_squares_iff

/-- A row index and a position within that row. -/
abbrev TriangleIndex (n : ℕ) := (i : Fin (n+1)) × Fin (i.val+1)

theorem card_triangleIndex (n : ℕ) :
    Fintype.card (TriangleIndex n) = (n+2)*(n+1)/2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t => t+1),Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  have h := Finset.sum_range_id (n+2)
  rw [Finset.sum_range_succ] at h
  rwa [show n+2-1 = n+1 by omega] at h

private def leftCoord {n : ℕ} (s : TriangleIndex n) : ℤ := -(s.2.val:ℤ)
private def rightCoord {n : ℕ} (s : TriangleIndex n) : ℤ := (s.2.val:ℤ)-s.1.val-1

/-- Integer quadratic representing one strictly interior trace-one element. -/
def interiorPolynomial {n : ℕ} (s : TriangleIndex n) : ℤ[X] :=
  coordinatePolynomial ((n:ℤ)+2) 1 (leftCoord s) (rightCoord s)

private theorem basis_separates {a b c : ℝ}
    (ht : ∀ u v w, weighted a b c (fun x => (traceBasis u v w x)^2) = u^2+v^2+w^2)
    {v w v' w' : ℝ}
    (ha : traceBasis 1 v w a = traceBasis 1 v' w' a)
    (hb : traceBasis 1 v w b = traceBasis 1 v' w' b)
    (hc : traceBasis 1 v w c = traceBasis 1 v' w' c) : v = v' ∧ w = w' := by
  have h0 (x : ℝ) (hx : traceBasis 1 v w x = traceBasis 1 v' w' x) :
      traceBasis 0 (v-v') (w-w') x = 0 := by
    unfold traceBasis at hx ⊢
    linear_combination hx
  have h := ht 0 (v-v') (w-w')
  simp only [weighted,h0 a ha,h0 b hb,h0 c hc,zero_pow (by norm_num : 2 ≠ 0),
    mul_zero,add_zero,zero_add] at h
  constructor <;> apply sub_eq_zero.mp <;> apply sq_eq_zero_iff.mp <;>
    linarith only [h,sq_nonneg (v-v'),sq_nonneg (w-w')]

private theorem index_injective (n : ℕ) {s t : TriangleIndex n}
    (hl : leftCoord s = leftCoord t) (hr : rightCoord s = rightCoord t) : s = t := by
  obtain ⟨i,j⟩ := s
  obtain ⟨i',j'⟩ := t
  simp only [leftCoord,rightCoord,neg_inj] at hl hr
  have he : i = i' := Fin.ext (by omega)
  subst i'
  have he' : j = j' := Fin.ext (by omega)
  subst j'
  rfl

/-- For m = n+2 there are at least m(m−1)/2 distinct totally positive
integral elements of trace one outside the cone of sums of squares.
Distinct indices already give different values on the three real roots. -/
theorem positive_trace_one_outside_squares (n : ℕ) :
    let m : ℝ := n+2
    let atRoot := fun (P : ℤ[X]) (x : ℝ) => P.eval₂ (Int.castRingHom ℝ) x
    ∃ a b c : ℝ, binary (m-1/2) a 1 = 0 ∧ binary (m-1/2) b 1 = 0 ∧ binary (m-1/2) c 1 = 0 ∧
      (∀ s : TriangleIndex n,
        let f := atRoot (interiorPolynomial s)
        0 < f a ∧ 0 < f b ∧ 0 < f c ∧ weighted a b c f = 1 ∧
          ∀ (k : ℕ) (P : Fin k → ℤ[X]), ¬ ∀ x, binary (m-1/2) x 1 = 0 → integralSquares P x = f x) ∧
      Function.Injective (fun s : TriangleIndex n =>
        let f := atRoot (interiorPolynomial s)
        (f a,f b,f c)) := by
  intro m atRoot
  let M : ℤ := n+2
  have hm : (M:ℝ) = m := by simp [M,m]
  obtain ⟨a,b,c,ha,hb,hc,ht,htri⟩ := triangular_trace_one n
  have hev (s : TriangleIndex n) (x : ℝ) (hx : binary (m-1/2) x 1 = 0) :
      atRoot (interiorPolynomial s) x = traceBasis 1 (leftCoord s) (rightCoord s) x := by
    simpa only [atRoot,interiorPolynomial,M,Int.cast_one,Nat.cast_add,Nat.cast_ofNat] using
      coordinatePolynomial_evaluation M 1 (leftCoord s) (rightCoord s) x
      (by rwa [hm])
  have sep (s : TriangleIndex n) (v w : ℝ)
      (h : ∀ x, binary (m-1/2) x 1 = 0 → atRoot (interiorPolynomial s) x = traceBasis 1 v w x) :
      (leftCoord s:ℝ) = v ∧ (rightCoord s:ℝ) = w :=
    basis_separates ht ((hev s a ha).symm.trans (h a ha))
      ((hev s b hb).symm.trans (h b hb)) ((hev s c hc).symm.trans (h c hc))
  refine ⟨a,b,c,ha,hb,hc,?_,?_⟩
  · intro s f
    have hrow := htri s.1 s.2
    have hcoords : (rightCoord s : ℝ) = -((s.1.val:ℝ)+1-s.2.val) := by
      simp [rightCoord]
      ring
    have he (x : ℝ) (hx : binary (m-1/2) x 1 = 0) :
        f x = traceBasis 1 (-(s.2.val:ℝ)) (-((s.1.val:ℝ)+1-s.2.val)) x := by
      simpa only [hcoords,leftCoord,Int.cast_neg,Int.cast_natCast] using hev s x hx
    have htrace : weighted a b c f = 1 := by
      exact (show weighted a b c f =
          weighted a b c (traceBasis 1 (-(s.2.val:ℝ)) (-((s.1.val:ℝ)+1-s.2.val))) by
            simp only [weighted,he a ha,he b hb,he c hc]).trans hrow.2.2.2
    refine ⟨(he a ha).symm ▸ hrow.1,(he b hb).symm ▸ hrow.2.1,
      (he c hc).symm ▸ hrow.2.2.1,htrace,?_⟩
    intro k P hP
    have hp : weighted a b c (integralSquares P) = 1 := by
      simpa only [weighted,hP a ha,hP b hb,hP c hc] using htrace
    have hclass := classify_squares (m := M) (a := a) (b := b) (c := c)
      (by rwa [hm]) (by rwa [hm]) (by rwa [hm]) ht P hp
    rw [hm] at hclass
    have hi := s.1.isLt
    have hj := s.2.isLt
    rcases hclass with h | h | h
    · obtain ⟨hl,hr⟩ := sep s 0 0 fun x hx => by
        simpa [traceBasis] using (hP x hx).symm.trans (h x hx)
      have hli : leftCoord s = 0 := by exact_mod_cast hl
      have hri : rightCoord s = 0 := by exact_mod_cast hr
      dsimp [leftCoord,rightCoord] at hli hri
      omega
    · have hl := (sep s (1-m) (-1) fun x hx =>
        ((hP x hx).symm.trans (h x hx)).trans (reciprocal_square_coordinates m x hx).1).1
      have hli : leftCoord s = 1-((n:ℤ)+2) := by dsimp [m] at hl; exact_mod_cast hl
      dsimp [leftCoord] at hli
      omega
    · have hl := (sep s 1 (-m) fun x hx =>
        ((hP x hx).symm.trans (h x hx)).trans (reciprocal_square_coordinates m x hx).2).1
      have hli : leftCoord s = 1 := by exact_mod_cast hl
      dsimp [leftCoord] at hli
      omega
  · intro s t he
    have H (x : ℝ) (hx : binary (m-1/2) x 1 = 0)
        (h : atRoot (interiorPolynomial s) x = atRoot (interiorPolynomial t) x) :=
      (hev s x hx).symm.trans (h.trans (hev t x hx))
    have ⟨hl,hr⟩ := basis_separates ht (H a ha (congrArg Prod.fst he))
      (H b hb (congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) he))
      (H c hc (congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) he))
    exact index_injective n (by exact_mod_cast hl) (by exact_mod_cast hr)

#print axioms card_triangleIndex
#print axioms positive_trace_one_outside_squares
end RHTower.OrbitCubic
