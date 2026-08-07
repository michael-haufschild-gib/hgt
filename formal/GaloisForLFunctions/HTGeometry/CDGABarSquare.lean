import GaloisForLFunctions.HTGeometry.CDGABarCancel
import GaloisForLFunctions.HTGeometry.CDGABarDifferential

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

/-- The target degree, from an outer split and a split of its first part. -/
theorem barSplit_first_eq {a a' c : ℕ} (hs : a + a' + 1 = c) (s' : BarSplit a) :
    s'.1.1 + s'.1.2 + 1 + a' + 1 = c := by
  obtain ⟨⟨u, u'⟩, hu⟩ := s'
  have h : u + u' + 1 = a := hu
  show u + u' + 1 + a' + 1 = c
  omega

/-- The component read, from an outer split and a split of its first part. -/
theorem barSplit_first_deg {a a' c e n : ℕ} (hs : a + a' + 1 = c) (hp : c + e = n + 1 + 1)
    (s' : BarSplit a) : s'.1.1 + (s'.1.2 + (a' + e)) = n := by
  obtain ⟨⟨u, u'⟩, hu⟩ := s'
  have h : u + u' + 1 = a := hu
  show u + (u' + (a' + e)) = n
  omega

/-- Tensoring a finite sum of maps with the identity. -/
theorem tensorMap_id_sum {M N N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] {ι : Type*} (s : Finset ι)
    (g : ι → (N →ₗ[R] N')) :
    TensorProduct.map (LinearMap.id (R := R) (M := M)) (∑ i ∈ s, g i)
      = ∑ i ∈ s, TensorProduct.map (LinearMap.id (R := R) (M := M)) (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, TensorProduct.map_zero_right]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, TensorProduct.map_add_right, ih]

/-- **The head applied twice, at one outer split, is a sum of first bracketings.** -/
theorem barHead_head_outer (n c e : ℕ) (hp : c + e = n + 1 + 1) (a a' : ℕ) (hs : a + a' + 1 = c)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z)) n) :
    barHeadTermₗ ε Z (n + 1) c e hp a a' hs
        (barHeadₗ ε (TensorCarrier (R := R) (barShiftFamily ε) Z) n F)
      = ∑ s' : BarSplit a, barMulFirstTwo ε (W := Z e)
        (rfl : s'.1.1 + s'.1.2 + 1 = s'.1.1 + s'.1.2 + 1) (barSplit_first_eq hs s')
        (barTele ε Z s'.1.1 s'.1.2 a' e
          (F ⟨(s'.1.1, s'.1.2 + (a' + e)), barSplit_first_deg hs hp s'⟩)) := by
  rw [barHeadTermₗ_eq_comp, barHead_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  obtain ⟨⟨u, u'⟩, hu⟩ := s'
  have hua : u + u' + 1 = a := hu
  subst hua
  rw [barHeadTermₗ_eq_comp]
  exact barHead_first_comp u u' a' e _ hs (F ⟨(u, u' + (a' + e)), by omega⟩)

/-- The target degree, from an outer split and a split of its second part. -/
theorem barSplit_second_eq {a a' c : ℕ} (hs : a + a' + 1 = c) (s'' : BarSplit a') :
    a + (s''.1.1 + s''.1.2 + 1) + 1 = c := by
  obtain ⟨⟨v, v'⟩, hv⟩ := s''
  have h : v + v' + 1 = a' := hv
  show a + (v + v' + 1) + 1 = c
  omega

/-- The component read, from an outer split and a split of its second part. -/
theorem barSplit_second_deg {a a' c e n : ℕ} (hs : a + a' + 1 = c) (hp : c + e = n + 1 + 1)
    (s'' : BarSplit a') : a + (s''.1.1 + (s''.1.2 + e)) = n := by
  obtain ⟨⟨v, v'⟩, hv⟩ := s''
  have h : v + v' + 1 = a' := hv
  show a + (v + (v' + e)) = n
  omega

/-- The component of the inner head that the outer term reads, as a sum over splits. -/
theorem barProj_comp_head (b' a' e : ℕ) (hq : a' + e = b' + 1) :
    (barProj (M := barShiftFamily ε) (N := Z) ⟨(a', e), hq.symm ▸ rfl⟩).comp
        (barHeadₗ ε Z b')
      = ∑ s'' : BarSplit a', barHeadTermₗ ε Z b' a' e (by omega) s''.1.1 s''.1.2 s''.2 := by
  refine LinearMap.ext fun V => ?_
  rw [LinearMap.comp_apply, LinearMap.sum_apply]
  exact barHead_apply ε Z b' V ⟨(a', e), by omega⟩

/-- The head after the tail, at one outer split whose second part and the trailing degree leave a
successor.  Stated with the index already a successor, so that the tail's defining equation applies
without moving anything. -/
theorem barHead_tail_succ (n c e : ℕ) (hp : c + e = n + 1 + 1) (a a' b' : ℕ)
    (hs : a + a' + 1 = c) (hb : a' + e = b' + 1) (hix : a + (b' + 1) = n + 1)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z)) n) :
    (TensorProduct.map (augIdealShiftMulOfTensor ε hs) (LinearMap.id (R := R) (M := Z e)))
        ((TensorProduct.assoc R (barShiftFamily ε a) (barShiftFamily ε a') (Z e)).symm
          ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
              (barProj (M := barShiftFamily ε) (N := Z) (n := b' + 1) ⟨(a', e), hb⟩))
            (tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barHeadₗ ε Z b) n F
              ⟨(a, b' + 1), hix⟩)))
      = ∑ s'' : BarSplit a', ((-1 : R)) ^ a • barMulLastTwo ε (W := Z e)
        (rfl : s''.1.1 + s''.1.2 + 1 = s''.1.1 + s''.1.2 + 1) (barSplit_second_eq hs s'')
        (barTele ε Z a s''.1.1 s''.1.2 e
          (F ⟨(a, s''.1.1 + (s''.1.2 + e)), barSplit_second_deg hs hp s''⟩)) := by
  rw [tensorRightDegOneₗ_succ, map_smul, map_smul, map_smul,
    ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id,
    show (barProj (M := barShiftFamily ε) (N := Z) (n := b' + 1) ⟨(a', e), hb⟩).comp
        (barHeadₗ ε Z b')
      = ∑ s'' : BarSplit a', barHeadTermₗ ε Z b' a' e (by omega) s''.1.1 s''.1.2 s''.2 from
      barProj_comp_head b' a' e hb,
    tensorMap_id_sum, LinearMap.sum_apply, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s'' _ => ?_
  obtain ⟨⟨v, v'⟩, hv⟩ := s''
  have hva : v + v' + 1 = a' := hv
  subst hva
  have hbv : b' = v + (v' + e) := by omega
  subst hbv
  exact congrArg (fun z => ((-1 : R)) ^ a • z)
    (barHead_second_comp a v v' e c (v + v' + 1) rfl hs (by omega)
      (F ⟨(a, v + (v' + e)), by omega⟩))

/-- **The head after the tail, at one outer split, is a sum of second bracketings.** -/
theorem barHead_tail_outer (n c e : ℕ) (hp : c + e = n + 1 + 1) (a a' : ℕ) (hs : a + a' + 1 = c)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z)) n) :
    barHeadTermₗ ε Z (n + 1) c e hp a a' hs
        (tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barHeadₗ ε Z b) n F)
      = ∑ s'' : BarSplit a', ((-1 : R)) ^ a • barMulLastTwo ε (W := Z e)
        (rfl : s''.1.1 + s''.1.2 + 1 = s''.1.1 + s''.1.2 + 1) (barSplit_second_eq hs s'')
        (barTele ε Z a s''.1.1 s''.1.2 e
          (F ⟨(a, s''.1.1 + (s''.1.2 + e)), barSplit_second_deg hs hp s''⟩)) := by
  rw [barHeadTermₗ_eq_comp]
  cases e with
  | succ e' =>
      exact barHead_tail_succ n c (e' + 1) hp a a' (a' + e') hs (by omega) (by omega) F
  | zero =>
      cases a' with
      | succ a'' =>
          exact barHead_tail_succ n c 0 hp a (a'' + 1) a'' hs (by omega) (by omega) F
      | zero =>
          have hempty : (Finset.univ : Finset (BarSplit 0)) = ∅ := by
            refine Finset.eq_empty_of_forall_notMem ?_
            rintro ⟨⟨v, v'⟩, hv⟩ -
            have hvv : v + v' + 1 = 0 := hv
            omega
          rw [hempty, Finset.sum_empty,
            show tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barHeadₗ ε Z b) n F
                ⟨(a, 0 + 0), by omega⟩ = 0 from
              tensorRightDegOneₗ_zero (M := barShiftFamily ε) (fun b => barHeadₗ ε Z b) n a F _,
            map_zero, map_zero, map_zero]

theorem barTripleOfFirst_bijective {c : ℕ} :
    Function.Bijective (barTripleOfFirst (c := c)) :=
  Function.bijective_iff_has_inverse.2
    ⟨barFirstOfTriple, barFirstOfTriple_barTripleOfFirst, barTripleOfFirst_barFirstOfTriple⟩

theorem barTripleOfSecond_bijective {c : ℕ} :
    Function.Bijective (barTripleOfSecond (c := c)) :=
  Function.bijective_iff_has_inverse.2
    ⟨barSecondOfTriple, barSecondOfTriple_barTripleOfSecond, barTripleOfSecond_barSecondOfTriple⟩

/-- **The square of the bar differential vanishes on three factors**, componentwise: the head
applied twice and the head after the tail cancel. -/
theorem barHead_sq_add (n c e : ℕ) (hp : c + e = n + 1 + 1)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z)) n) :
    barHeadₗ ε Z (n + 1)
        (barHeadₗ ε (TensorCarrier (R := R) (barShiftFamily ε) Z) n F) ⟨(c, e), hp⟩
      + barHeadₗ ε Z (n + 1)
        (tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barHeadₗ ε Z b) n F)
        ⟨(c, e), hp⟩ = 0 := by
  rw [barHead_apply, barHead_apply]
  simp only [barHead_head_outer, barHead_tail_outer]
  rw [Finset.sum_sigma' Finset.univ (fun _ => Finset.univ), Finset.sum_sigma' Finset.univ
    (fun _ => Finset.univ)]
  rw [Finset.sum_nbij'
    (s := Finset.univ.sigma fun _ : BarSplit c => (Finset.univ : Finset _))
    (t := Finset.univ.sigma fun _ : BarSplit c => (Finset.univ : Finset _))
    (f := fun τ : (s : BarSplit c) × BarSplit s.1.2 =>
      ((-1 : R)) ^ τ.1.1.1 • barMulLastTwo ε (W := Z e)
        (rfl : τ.2.1.1 + τ.2.1.2 + 1 = τ.2.1.1 + τ.2.1.2 + 1) (barSplit_second_eq τ.1.2 τ.2)
        (barTele ε Z τ.1.1.1 τ.2.1.1 τ.2.1.2 e
          (F ⟨(τ.1.1.1, τ.2.1.1 + (τ.2.1.2 + e)), barSplit_second_deg τ.1.2 hp τ.2⟩)))
    (g := fun σ : (s : BarSplit c) × BarSplit s.1.1 =>
      ((-1 : R)) ^ (barSecondOfTriple (barTripleOfFirst σ)).1.1.1 • barMulLastTwo ε (W := Z e)
        (rfl : (barSecondOfTriple (barTripleOfFirst σ)).2.1.1
            + (barSecondOfTriple (barTripleOfFirst σ)).2.1.2 + 1
          = (barSecondOfTriple (barTripleOfFirst σ)).2.1.1
            + (barSecondOfTriple (barTripleOfFirst σ)).2.1.2 + 1)
        (barSplit_second_eq (barSecondOfTriple (barTripleOfFirst σ)).1.2
          (barSecondOfTriple (barTripleOfFirst σ)).2)
        (barTele ε Z (barSecondOfTriple (barTripleOfFirst σ)).1.1.1
          (barSecondOfTriple (barTripleOfFirst σ)).2.1.1
          (barSecondOfTriple (barTripleOfFirst σ)).2.1.2 e
          (F ⟨((barSecondOfTriple (barTripleOfFirst σ)).1.1.1,
            (barSecondOfTriple (barTripleOfFirst σ)).2.1.1
              + ((barSecondOfTriple (barTripleOfFirst σ)).2.1.2 + e)),
            barSplit_second_deg (barSecondOfTriple (barTripleOfFirst σ)).1.2 hp
              (barSecondOfTriple (barTripleOfFirst σ)).2⟩)))
    (fun τ => barFirstOfTriple (barTripleOfSecond τ))
    (fun σ => barSecondOfTriple (barTripleOfFirst σ))
    (fun a _ => Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun a _ => Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun a _ => by
      rw [barTripleOfFirst_barFirstOfTriple, barSecondOfTriple_barTripleOfSecond])
    (fun a _ => by
      rw [barTripleOfSecond_barSecondOfTriple, barFirstOfTriple_barTripleOfFirst])
    (fun a _ => by
      rw [barTripleOfFirst_barFirstOfTriple, barSecondOfTriple_barTripleOfSecond])]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun σ _ => ?_
  exact barTriple_cancel n c e hp (barTripleOfFirst σ) F

/-- **The head applied twice and the head after the tail cancel**, as maps. -/
theorem barHead_sq (n : ℕ)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z)) n) :
    barHeadₗ ε Z (n + 1)
        (barHeadₗ ε (TensorCarrier (R := R) (barShiftFamily ε) Z) n F
          + tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barHeadₗ ε Z b) n F) = 0 := by
  rw [map_add]
  funext p
  obtain ⟨⟨c, e⟩, hp⟩ := p
  exact barHead_sq_add n c e hp F

/-- **The bar differential squares to zero on three factors.** -/
theorem barD_two_sq (n : ℕ) (F : (barPower ε 3).carrier n) :
    barD ε 1 (n + 1) (barD ε 2 n F) = 0 := by
  have htail : (fun b => barD ε 1 b)
      = fun b => barHeadₗ ε (barPower ε 0).carrier b := funext fun b => barD_one_eq ε b
  have hd2 : barD ε 2 n F
      = (show TensorCarrier (R := R) (barShiftFamily ε)
            (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε 0).carrier) (n + 1) from
          barHeadₗ ε (barPower ε 1).carrier n F)
        + tensorRightDegOneₗ (M := barShiftFamily ε)
          (fun b => barHeadₗ ε (barPower ε 0).carrier b) n F := by
    rw [barD_succ, ← htail]
    rfl
  rw [barD_one_eq, hd2]
  exact barHead_sq (Z := (barPower ε 0).carrier) n F

end Assembly

end Identification

end GaloisForLFunctions.HTGeometry
