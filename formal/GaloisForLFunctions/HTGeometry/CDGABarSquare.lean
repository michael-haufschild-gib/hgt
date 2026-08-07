import GaloisForLFunctions.HTGeometry.CDGABarCancel

/-!
# The double sum of the bar square

The square of the bar differential on three or more factors is a double sum: an outer split of the
target degree and, inside it, either a further split of the first part — that is the head applied
twice — or a split of the second part — that is the head after the tail.  Both are indexed by the
triples of degrees the two multiplications consume, and both read the same component of the
argument, so they can be compared term by term.

* `HTGeometry.BarTriple` : the triples of degrees two multiplications consume.
* `HTGeometry.barTripleOfFirst`, `HTGeometry.barTripleOfSecond` : the two reindexings.
* `HTGeometry.barTele` : the component of the argument both sides read.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))
  (Z : ℕ → Type u) [∀ n, AddCommGroup (Z n)] [∀ n, Module R (Z n)]

/-- The ways a shifted degree is consumed by two multiplications of three adjacent factors. -/
abbrev BarTriple (c : ℕ) : Type := {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + t.2.2 + 2 = c}

/-- An outer split together with a split of its first part is a triple. -/
def barTripleOfFirst {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.1) : BarTriple c :=
  ⟨(s.2.1.1, s.2.1.2, s.1.1.2), by
    obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
    have h1 : a + a' + 1 = c := hs
    have h2 : v + v' + 1 = a := hv
    show v + v' + a' + 2 = c
    omega⟩

/-- A triple is an outer split together with a split of its first part. -/
def barFirstOfTriple {c : ℕ} (t : BarTriple c) : Σ s : BarSplit c, BarSplit s.1.1 :=
  ⟨⟨(t.1.1 + t.1.2.1 + 1, t.1.2.2), by
    obtain ⟨⟨a, b, d⟩, ht⟩ := t
    have h : a + b + d + 2 = c := ht
    show a + b + 1 + d + 1 = c
    omega⟩, ⟨(t.1.1, t.1.2.1), rfl⟩⟩

/-- An outer split together with a split of its second part is a triple. -/
def barTripleOfSecond {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.2) : BarTriple c :=
  ⟨(s.1.1.1, s.2.1.1, s.2.1.2), by
    obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
    have h1 : a + a' + 1 = c := hs
    have h2 : v + v' + 1 = a' := hv
    show a + v + v' + 2 = c
    omega⟩

/-- A triple is an outer split together with a split of its second part. -/
def barSecondOfTriple {c : ℕ} (t : BarTriple c) : Σ s : BarSplit c, BarSplit s.1.2 :=
  ⟨⟨(t.1.1, t.1.2.1 + t.1.2.2 + 1), by
    obtain ⟨⟨a, b, d⟩, ht⟩ := t
    have h : a + b + d + 2 = c := ht
    show a + (b + d + 1) + 1 = c
    omega⟩, ⟨(t.1.2.1, t.1.2.2), rfl⟩⟩

theorem barTripleOfFirst_barFirstOfTriple {c : ℕ} (t : BarTriple c) :
    barTripleOfFirst (barFirstOfTriple t) = t := by
  obtain ⟨⟨a, b, d⟩, h⟩ := t
  rfl

theorem barFirstOfTriple_barTripleOfFirst {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.1) :
    barFirstOfTriple (barTripleOfFirst s) = s := by
  obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
  have ha : v + v' + 1 = a := hv
  subst ha
  rfl

theorem barTripleOfSecond_barSecondOfTriple {c : ℕ} (t : BarTriple c) :
    barTripleOfSecond (barSecondOfTriple t) = t := by
  obtain ⟨⟨a, b, d⟩, h⟩ := t
  rfl

theorem barSecondOfTriple_barTripleOfSecond {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.2) :
    barSecondOfTriple (barTripleOfSecond s) = s := by
  obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
  have ha : v + v' + 1 = a' := hv
  subst ha
  rfl

/-- **The component of the argument that both halves of the square read**, with its three shifted
factors separated. -/
noncomputable def barTele (u u' w e : ℕ) :
    TensorProduct R (barShiftFamily ε u)
        (TensorCarrier (R := R) (barShiftFamily ε)
          (TensorCarrier (R := R) (barShiftFamily ε) Z) (u' + (w + e)))
      →ₗ[R] TensorProduct R (barShiftFamily ε u)
        (TensorProduct R (barShiftFamily ε u') (TensorProduct R (barShiftFamily ε w) (Z e))) :=
  TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u))
    ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u'))
        (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = w + e} =>
          TensorProduct R (barShiftFamily ε q.1.1) (Z q.1.2)) ⟨(w, e), rfl⟩)).comp
      (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = u' + (w + e)} =>
        TensorProduct R (barShiftFamily ε q.1.1)
          (TensorCarrier (R := R) (barShiftFamily ε) Z q.1.2)) ⟨(u', w + e), rfl⟩))

section Identification

variable {ε} {Z}

/-- Abbreviation for the family of shifted factors. -/
local notation "S" => barShiftFamily ε

/-- The projection of a graded tensor product at a bidegree. -/
noncomputable abbrev barProj {M N : ℕ → Type u} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)] {n : ℕ}
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    TensorCarrier (R := R) M N n →ₗ[R] TensorProduct R (M p.1.1) (N p.1.2) :=
  LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = n} =>
    TensorProduct R (M q.1.1) (N q.1.2)) p

/-- **The projection of the innermost factor commutes past a multiplication of the outer two.**
This is the only thing separating the head applied twice from the first bracketing of the telescope:
the multiplications act on the outer factors and the projection on the inner one. -/
theorem barProj_comm_mul (u u' w e : ℕ)
    (T : TensorProduct R (barShiftFamily ε u)
      (TensorProduct R (barShiftFamily ε u')
        (TensorCarrier (R := R) (barShiftFamily ε) Z (w + e)))) :
    (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε (u + u' + 1)))
        (barProj (M := barShiftFamily ε) (N := Z) ⟨(w, e), rfl⟩))
        ((TensorProduct.map (augIdealShiftMulOfTensor ε (rfl : u + u' + 1 = u + u' + 1))
            (LinearMap.id (R := R)
              (M := TensorCarrier (R := R) (barShiftFamily ε) Z (w + e))))
          ((TensorProduct.assoc R (barShiftFamily ε u) (barShiftFamily ε u')
            (TensorCarrier (R := R) (barShiftFamily ε) Z (w + e))).symm T))
      = (TensorProduct.map (augIdealShiftMulOfTensor ε (rfl : u + u' + 1 = u + u' + 1))
          (LinearMap.id (R := R) (M := TensorProduct R (barShiftFamily ε w) (Z e))))
        ((TensorProduct.assoc R (barShiftFamily ε u) (barShiftFamily ε u')
            (TensorProduct R (barShiftFamily ε w) (Z e))).symm
          (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u))
            (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u'))
              (barProj (M := barShiftFamily ε) (N := Z) ⟨(w, e), rfl⟩)) T)) := by
  induction T using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add T T' hT hT' =>
      simp only [map_add]
      rw [hT, hT']
  | tmul x V =>
      induction V using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add V V' hV hV' =>
          simp only [TensorProduct.tmul_add, map_add]
          rw [hV, hV']
      | tmul y P => rfl

/-- **The head applied twice, at one pair of splits, is the first bracketing of the telescope.** -/
theorem barHead_first_comp (u u' w e c : ℕ) (hs : u + u' + 1 + w + 1 = c)
    (G : TensorProduct R (barShiftFamily ε u)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z) (u' + (w + e)))) :
    (TensorProduct.map (augIdealShiftMulOfTensor ε hs) (LinearMap.id (R := R) (M := Z e)))
        ((TensorProduct.assoc R (barShiftFamily ε (u + u' + 1)) (barShiftFamily ε w) (Z e)).symm
          ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε (u + u' + 1)))
              (barProj (M := barShiftFamily ε) (N := Z) ⟨(w, e), rfl⟩))
            ((TensorProduct.map (augIdealShiftMulOfTensor ε (rfl : u + u' + 1 = u + u' + 1))
                (LinearMap.id (R := R)
                  (M := TensorCarrier (R := R) (barShiftFamily ε) Z (w + e))))
              ((TensorProduct.assoc R (barShiftFamily ε u) (barShiftFamily ε u')
                  (TensorCarrier (R := R) (barShiftFamily ε) Z (w + e))).symm
                ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u))
                    (barProj (M := barShiftFamily ε)
                      (N := TensorCarrier (R := R) (barShiftFamily ε) Z) ⟨(u', w + e), rfl⟩))
                  G)))))
      = barMulFirstTwo ε (W := Z e) (rfl : u + u' + 1 = u + u' + 1) hs
        (barTele ε Z u u' w e G) := by
  rw [barProj_comm_mul]
  have htele : (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u))
        (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u'))
          (barProj (M := barShiftFamily ε) (N := Z) ⟨(w, e), rfl⟩)))
      ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u))
        (barProj (M := barShiftFamily ε)
          (N := TensorCarrier (R := R) (barShiftFamily ε) Z) ⟨(u', w + e), rfl⟩)) G)
      = barTele ε Z u u' w e G := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
    rfl
  rw [htele]
  rfl

/-- **The head after the tail, at one pair of splits, is the second bracketing of the telescope.**
Here nothing has to be commuted: the tail multiplies inside the second factor, exactly where the
telescope's projections already are. -/
theorem barHead_second_comp (u u' w e c m' : ℕ) (h₃ : u' + w + 1 = m') (h₄ : u + m' + 1 = c)
    (hq : m' + e = u' + (w + e) + 1)
    (G : TensorProduct R (barShiftFamily ε u)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z) (u' + (w + e)))) :
    (TensorProduct.map (augIdealShiftMulOfTensor ε h₄) (LinearMap.id (R := R) (M := Z e)))
        ((TensorProduct.assoc R (barShiftFamily ε u) (barShiftFamily ε m') (Z e)).symm
          (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u))
            (barHeadTermₗ ε Z (u' + (w + e)) m' e hq u' w h₃) G))
      = barMulLastTwo ε (W := Z e) h₃ h₄ (barTele ε Z u u' w e G) := by
  induction G using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add G G' hG hG' =>
      simp only [map_add]
      rw [hG, hG']
  | tmul x M => rfl

/-- One term of the head, as the outer map applied to the component it reads. -/
theorem barHeadTermₗ_eq_comp (n c e : ℕ) (hp : c + e = n + 1) (a a' : ℕ) (hs : a + a' + 1 = c)
    (V : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    barHeadTermₗ ε Z n c e hp a a' hs V
      = (TensorProduct.map (augIdealShiftMulOfTensor ε hs) (LinearMap.id (R := R) (M := Z e)))
        ((TensorProduct.assoc R (barShiftFamily ε a) (barShiftFamily ε a') (Z e)).symm
          ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
              (barProj (M := barShiftFamily ε) (N := Z) ⟨(a', e), rfl⟩))
            (V ⟨(a, a' + e), by omega⟩))) := rfl

section Assembly

/-- The outer split a triple determines when the first two factors are multiplied first. -/
theorem barTriple_first_eq {c : ℕ} (t : BarTriple c) :
    t.1.1 + t.1.2.1 + 1 + t.1.2.2 + 1 = c := by
  obtain ⟨⟨a, b, d⟩, ht⟩ := t
  have h : a + b + d + 2 = c := ht
  show a + b + 1 + d + 1 = c
  omega

/-- The outer split a triple determines when the last two factors are multiplied first. -/
theorem barTriple_second_eq {c : ℕ} (t : BarTriple c) :
    t.1.1 + (t.1.2.1 + t.1.2.2 + 1) + 1 = c := by
  obtain ⟨⟨a, b, d⟩, ht⟩ := t
  have h : a + b + d + 2 = c := ht
  show a + (b + d + 1) + 1 = c
  omega

/-- The component of the argument a triple reads. -/
theorem barTriple_deg {n c e : ℕ} (hp : c + e = n + 1 + 1) (t : BarTriple c) :
    t.1.1 + (t.1.2.1 + (t.1.2.2 + e)) = n := by
  obtain ⟨⟨a, b, d⟩, ht⟩ := t
  have h : a + b + d + 2 = c := ht
  show a + (b + (d + e)) = n
  omega

/-- **The two halves of the bar square cancel, triple by triple.** -/
theorem barTriple_cancel (n c e : ℕ) (hp : c + e = n + 1 + 1) (t : BarTriple c)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z) ) n) :
    barMulFirstTwo ε (W := Z e) (rfl : t.1.1 + t.1.2.1 + 1 = t.1.1 + t.1.2.1 + 1)
        (barTriple_first_eq t)
        (barTele ε Z t.1.1 t.1.2.1 t.1.2.2 e (F ⟨(t.1.1, t.1.2.1 + (t.1.2.2 + e)),
          barTriple_deg hp t⟩))
      + ((-1 : R)) ^ t.1.1 • barMulLastTwo ε (W := Z e)
        (rfl : t.1.2.1 + t.1.2.2 + 1 = t.1.2.1 + t.1.2.2 + 1) (barTriple_second_eq t)
        (barTele ε Z t.1.1 t.1.2.1 t.1.2.2 e (F ⟨(t.1.1, t.1.2.1 + (t.1.2.2 + e)),
          barTriple_deg hp t⟩)) = 0 :=
  barMul_cancel ε _ _ _ _ _

end Assembly

end Identification

end GaloisForLFunctions.HTGeometry
