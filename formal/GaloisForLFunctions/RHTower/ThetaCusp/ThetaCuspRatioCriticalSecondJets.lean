import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCriticalFirstJet
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare
@[simp] private theorem pd_ofNat71 (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

private def scaled10Part0LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part0Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part0Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part0Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part0Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part1LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part1Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part1Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part1Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part1Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part2LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part2Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part2Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part2Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part2Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part3LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part3Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part3Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part3Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part3Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part4LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part4Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part4Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part4Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part4Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part5LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part5Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part5Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part5Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part5Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part6LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part6Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part6Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part6Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part6Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part7LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part7Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part7Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part7Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part7Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part8LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part8Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part8Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part8Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part8Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part9LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part9Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part9Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part9Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part9Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part10LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part10Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part10Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part10Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part10Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part11LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part11Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part11Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part11Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part11Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part12LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part12Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part12Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part12Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part12Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part13LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part13Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part13Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part13Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part13Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part14LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part14Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part14Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part14Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part14Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part15LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part15Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part15Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part15Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part15Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part16LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part16Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part16Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part16Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part16Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part17LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part17Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part17Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part17Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part17Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part18LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part18Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part18Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part18Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part18Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part19LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part19Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part19Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part19Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part19Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part20LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part20Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part20Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part20Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part20Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part21LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part21Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part21Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part21Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part21Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part22LowUUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part22Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part22Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaled10Part22Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part22Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def midScaled10UUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U midScaled10))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U midScaled10))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U midScaled10)) := rfl
  conv at he =>
    rhs
    norm_num [midScaled10,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def upperScaled10UUNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U upperScaled10))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U upperScaled10))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U upperScaled10)) := rfl
  conv at he =>
    rhs
    norm_num [upperScaled10,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def jet10UU (r : ℂ) : ℂ := eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.U scaledMoment10))
def jet10UUNorm (r : ℂ) : {c : ℂ // jet10UU r=c} := by
  have he : jet10UU r=jet10UU r := rfl
  conv at he =>
    rhs
    simp only [jet10UU,scaledMoment10,low10,map_add,(scaled10Part0LowUUNorm r).property,(scaled10Part1LowUUNorm r).property,(scaled10Part2LowUUNorm r).property,(scaled10Part3LowUUNorm r).property,(scaled10Part4LowUUNorm r).property,(scaled10Part5LowUUNorm r).property,(scaled10Part6LowUUNorm r).property,(scaled10Part7LowUUNorm r).property,(scaled10Part8LowUUNorm r).property,(scaled10Part9LowUUNorm r).property,(scaled10Part10LowUUNorm r).property,(scaled10Part11LowUUNorm r).property,(scaled10Part12LowUUNorm r).property,(scaled10Part13LowUUNorm r).property,(scaled10Part14LowUUNorm r).property,(scaled10Part15LowUUNorm r).property,(scaled10Part16LowUUNorm r).property,(scaled10Part17LowUUNorm r).property,(scaled10Part18LowUUNorm r).property,(scaled10Part19LowUUNorm r).property,(scaled10Part20LowUUNorm r).property,(scaled10Part21LowUUNorm r).property,(scaled10Part22LowUUNorm r).property,(midScaled10UUNorm r).property,(upperScaled10UUNorm r).property]
    norm_num [scaled10Part0LowUUNorm,scaled10Part1LowUUNorm,scaled10Part2LowUUNorm,scaled10Part3LowUUNorm,scaled10Part4LowUUNorm,scaled10Part5LowUUNorm,scaled10Part6LowUUNorm,scaled10Part7LowUUNorm,scaled10Part8LowUUNorm,scaled10Part9LowUUNorm,scaled10Part10LowUUNorm,scaled10Part11LowUUNorm,scaled10Part12LowUUNorm,scaled10Part13LowUUNorm,scaled10Part14LowUUNorm,scaled10Part15LowUUNorm,scaled10Part16LowUUNorm,scaled10Part17LowUUNorm,scaled10Part18LowUUNorm,scaled10Part19LowUUNorm,scaled10Part20LowUUNorm,scaled10Part21LowUUNorm,scaled10Part22LowUUNorm,midScaled10UUNorm,upperScaled10UUNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part0LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part0Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part0Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part0Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part0Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part1LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part1Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part1Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part1Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part1Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part2LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part2Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part2Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part2Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part2Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part3LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part3Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part3Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part3Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part3Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part4LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part4Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part4Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part4Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part4Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part5LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part5Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part5Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part5Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part5Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part6LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part6Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part6Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part6Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part6Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part7LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part7Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part7Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part7Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part7Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part8LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part8Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part8Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part8Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part8Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part9LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part9Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part9Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part9Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part9Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part10LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part10Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part10Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part10Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part10Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part11LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part11Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part11Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part11Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part11Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part12LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part12Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part12Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part12Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part12Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part13LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part13Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part13Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part13Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part13Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part14LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part14Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part14Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part14Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part14Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part15LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part15Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part15Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part15Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part15Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part16LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part16Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part16Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part16Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part16Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part17LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part17Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part17Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part17Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part17Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part18LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part18Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part18Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part18Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part18Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part19LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part19Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part19Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part19Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part19Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part20LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part20Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part20Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part20Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part20Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part21LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part21Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part21Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part21Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part21Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part22LowUJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part22Low))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part22Low))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaled10Part22Low)) := rfl
  conv at he =>
    rhs
    norm_num [scaled10Part22Low,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def midScaled10UJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J midScaled10))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J midScaled10))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J midScaled10)) := rfl
  conv at he =>
    rhs
    norm_num [midScaled10,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def upperScaled10UJNorm (r : ℂ) : {c : ℂ // eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J upperScaled10))=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J upperScaled10))=eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J upperScaled10)) := rfl
  conv at he =>
    rhs
    norm_num [upperScaled10,driftSquare,deficit,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def jet10UJ (r : ℂ) : ℂ := eval (basePoint 0 r (r/12)) (pderiv Coord.U (pderiv Coord.J scaledMoment10))
def jet10UJNorm (r : ℂ) : {c : ℂ // jet10UJ r=c} := by
  have he : jet10UJ r=jet10UJ r := rfl
  conv at he =>
    rhs
    simp only [jet10UJ,scaledMoment10,low10,map_add,(scaled10Part0LowUJNorm r).property,(scaled10Part1LowUJNorm r).property,(scaled10Part2LowUJNorm r).property,(scaled10Part3LowUJNorm r).property,(scaled10Part4LowUJNorm r).property,(scaled10Part5LowUJNorm r).property,(scaled10Part6LowUJNorm r).property,(scaled10Part7LowUJNorm r).property,(scaled10Part8LowUJNorm r).property,(scaled10Part9LowUJNorm r).property,(scaled10Part10LowUJNorm r).property,(scaled10Part11LowUJNorm r).property,(scaled10Part12LowUJNorm r).property,(scaled10Part13LowUJNorm r).property,(scaled10Part14LowUJNorm r).property,(scaled10Part15LowUJNorm r).property,(scaled10Part16LowUJNorm r).property,(scaled10Part17LowUJNorm r).property,(scaled10Part18LowUJNorm r).property,(scaled10Part19LowUJNorm r).property,(scaled10Part20LowUJNorm r).property,(scaled10Part21LowUJNorm r).property,(scaled10Part22LowUJNorm r).property,(midScaled10UJNorm r).property,(upperScaled10UJNorm r).property]
    norm_num [scaled10Part0LowUJNorm,scaled10Part1LowUJNorm,scaled10Part2LowUJNorm,scaled10Part3LowUJNorm,scaled10Part4LowUJNorm,scaled10Part5LowUJNorm,scaled10Part6LowUJNorm,scaled10Part7LowUJNorm,scaled10Part8LowUJNorm,scaled10Part9LowUJNorm,scaled10Part10LowUJNorm,scaled10Part11LowUJNorm,scaled10Part12LowUJNorm,scaled10Part13LowUJNorm,scaled10Part14LowUJNorm,scaled10Part15LowUJNorm,scaled10Part16LowUJNorm,scaled10Part17LowUJNorm,scaled10Part18LowUJNorm,scaled10Part19LowUJNorm,scaled10Part20LowUJNorm,scaled10Part21LowUJNorm,scaled10Part22LowUJNorm,midScaled10UJNorm,upperScaled10UJNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def jet10JJ (r : ℂ) : ℂ := eval (basePoint 0 r (r/12)) (pderiv Coord.J (pderiv Coord.J scaledMoment10))
def jet10JJNorm (r : ℂ) : {c : ℂ // jet10JJ r=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : jet10JJ r=jet10JJ r := rfl
  conv at he =>
    rhs
    norm_num [jet10JJ,scaledMoment10,low10,midScaled10,upperScaled10,
      driftSquare,deficit,scaled10Part0Low,scaled10Part1Low,scaled10Part2Low,scaled10Part3Low,scaled10Part4Low,scaled10Part5Low,scaled10Part6Low,scaled10Part7Low,scaled10Part8Low,scaled10Part9Low,scaled10Part10Low,scaled10Part11Low,scaled10Part12Low,scaled10Part13Low,scaled10Part14Low,scaled10Part15Low,scaled10Part16Low,scaled10Part17Low,scaled10Part18Low,scaled10Part19Low,scaled10Part20Low,scaled10Part21Low,scaled10Part22Low,
      pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def jet8U (r : ℂ) : ℂ := eval (basePoint 0 r (r/12)) (pderiv Coord.U scaledMoment8)
def jet8UNorm (r : ℂ) : {c : ℂ // jet8U r=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : jet8U r=jet8U r := rfl
  conv at he =>
    rhs
    norm_num [jet8U,scaledMoment8,low8,midScaled8,upperScaled8,
      driftSquare,deficit,scaled8Part0Low,scaled8Part1Low,scaled8Part2Low,scaled8Part3Low,scaled8Part4Low,scaled8Part5Low,scaled8Part6Low,scaled8Part7Low,scaled8Part8Low,scaled8Part9Low,scaled8Part10Low,scaled8Part11Low,scaled8Part12Low,scaled8Part13Low,
      pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
