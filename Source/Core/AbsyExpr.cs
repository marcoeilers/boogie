//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// BoogiePL - Absy.cs
//---------------------------------------------------------------------------------------------

namespace Microsoft.Boogie {
  using System;
  using System.Collections;
  using System.Diagnostics;
  using System.Collections.Generic;
  using Microsoft.Boogie.AbstractInterpretation;
  using System.Diagnostics.Contracts;
  using System.Linq;
  using Microsoft.Basetypes;

  using Set = GSet<object>; // not that the set used is not a set of Variable only, as it also contains TypeVariables


  //---------------------------------------------------------------------
  // Expressions
  //
  // For expressions, we override the Equals and GetHashCode method to
  // implement structural equality.  Note this is not logical equivalence
  // and is not modulo alpha-renaming.
  //---------------------------------------------------------------------


  [ContractClass(typeof(ExprContracts))]
  public abstract class Expr : Absy {
    public Expr(IToken/*!*/ tok, bool immutable)
      : base(tok) {
      Contract.Requires(tok != null);
      this.Immutable = immutable;
    }

    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      Emit(stream, 0, false);
    }

    /// <summary>
    /// If true the client is making a promise that this Expr will be
    /// treated immutably (i.e. once constructed it is never changed).
    /// This is currently not enforced but it should be!
    ///
    /// This allows the Expr's hash code to be cached making calls to
    /// GetHashCode() very cheap.
    /// </summary>
    /// <value><c>true</c> if immutable; otherwise, <c>false</c>.</value>
    public bool Immutable {
      get;
      private set;
    }

    /// <summary>
    /// Computes the hash code of this Expr skipping any cache.
    ///
    /// Sub classes should place their implementation of computing their hashcode
    /// here (making sure to call GetHashCode() not ComputeHashCode() on Expr for performance reasons)
    /// and have GetHashCode() use a cached result from ComputeHashCode() if the
    /// Expr was constructed to be immutable.
    /// </summary>
    /// <returns>The hash code.</returns>
    public abstract int ComputeHashCode();
    protected int CachedHashCode = 0;

    public abstract void Emit(TokenTextWriter/*!*/ wr, int contextBindingStrength, bool fragileContext);

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      System.IO.StringWriter buffer = new System.IO.StringWriter();
      using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, /*setTokens=*/ false, /*pretty=*/ false)) {
        this.Emit(stream, 0, false);
      }
      return buffer.ToString();
    }

    /// <summary>
    /// Add to "freeVars" the free variables in the expression.
    /// </summary>
    public abstract void ComputeFreeVariables(Set /*Variable*//*!*/ freeVars);

    /// <summary>
    /// Filled in by the Typecheck method.  A value of "null" means a succeeding
    /// call to Typecheck has not taken place (that is, either Typecheck hasn't
    /// been called or Typecheck encountered an error in the expression to be
    /// typechecked).
    /// </summary>
    private Type _Type = null;
    public Type Type {
      get {
        return _Type;
      }
      set {
        if (_Type == null) {
          // Expr has never been type checked so always allow this
          _Type = value;
        } else  {
          if (Immutable && !_Type.Equals(value))
            throw new InvalidOperationException("Cannot change the Type of an Immutable Expr");

          // Once the Type has been set (i.e. no longer null) we never change the reference 
          // if this Expr is immutable, even if the Type is equivalent (i.e. _Type.Equals(newType))
          if (!Immutable)
            _Type = value;
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      Contract.Ensures(Type != null);
      // This body is added only because C# insists on it.  It should really be left out, as if TypeCheck still were abstract.
      // The reason for mentioning the method here at all is to give TypeCheck a postcondition for all expressions.
      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    /// <summary>
    /// Returns the type of the expression, supposing that all its subexpressions are well typed.
    /// </summary>
    public abstract Type/*!*/ ShallowType {
      get;
    }

    // Handy syntactic sugar follows:

    public static NAryExpr Unary(IToken x, UnaryOperator.Opcode op, Expr e1) {
      Contract.Requires(e1 != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return new NAryExpr(x, new UnaryOperator(x, op), new List<Expr> { e1 });
    }

    public static NAryExpr Binary(IToken x, BinaryOperator.Opcode op, Expr e0, Expr e1) {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return new NAryExpr(x, new BinaryOperator(x, op), new List<Expr> { e0, e1 });
    }

    public static NAryExpr Binary(BinaryOperator.Opcode op, Expr e0, Expr e1) {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(Token.NoToken, op, e0, e1);
    }

    public static NAryExpr Eq(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Eq, e1, e2);
    }
    public static NAryExpr Neq(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Neq, e1, e2);
    }
    public static NAryExpr Le(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Le, e1, e2);
    }
    public static NAryExpr Ge(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Ge, e1, e2);
    }
    public static NAryExpr Lt(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Lt, e1, e2);
    }
    public static NAryExpr Gt(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Gt, e1, e2);
    }
    public static Expr And(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      if (e1 == true_) {
        return e2;
      } else if (e2 == true_) {
        return e1;
      } else if (e1 == false_ || e2 == false_) {
        return false_;
      } else {
        var res = Binary(BinaryOperator.Opcode.And, e1, e2);
        res.Type = Microsoft.Boogie.Type.Bool;
        res.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        return res;
      }
    }
    public static Expr Or(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      if (e1 == false_) {
        return e2;
      } else if (e2 == false_) {
        return e1;
      } else if (e1 == true_ || e2 == true_) {
        return true_;
      } else {
        return Binary(BinaryOperator.Opcode.Or, e1, e2);
      }
    }
    public static Expr Not(Expr e1) {
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      NAryExpr nary = e1 as NAryExpr;

      if (e1 == true_) {
        return false_;
      } else if (e1 == false_) {
        return true_;
      } else if (nary != null) {
        if (nary.Fun is UnaryOperator) {
          UnaryOperator op = (UnaryOperator)nary.Fun;
          if (op.Op == UnaryOperator.Opcode.Not) {
            return cce.NonNull(nary.Args[0]);
          }
        } else if (nary.Fun is BinaryOperator) {
          BinaryOperator op = (BinaryOperator)nary.Fun;
          Expr arg0 = cce.NonNull(nary.Args[0]);
          Expr arg1 = cce.NonNull(nary.Args[1]);
          if (op.Op == BinaryOperator.Opcode.Eq) {
            return Neq(arg0, arg1);
          } else if (op.Op == BinaryOperator.Opcode.Neq) {
            return Eq(arg0, arg1);
          } else if (op.Op == BinaryOperator.Opcode.Lt) {
            return Le(arg1, arg0);
          } else if (op.Op == BinaryOperator.Opcode.Le) {
            return Lt(arg1, arg0);
          } else if (op.Op == BinaryOperator.Opcode.Ge) {
            return Gt(arg1, arg0);
          } else if (op.Op == BinaryOperator.Opcode.Gt) {
            return Ge(arg1, arg0);
          }
        }
      }

      return Unary(Token.NoToken, UnaryOperator.Opcode.Not, e1);
    }

    public static Expr Neg(Expr e1) {
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return Unary(Token.NoToken, UnaryOperator.Opcode.Neg, e1);
    }

    public static NAryExpr Imp(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Imp, e1, e2);
    }
    public static NAryExpr Iff(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Iff, e1, e2);
    }
    public static NAryExpr Add(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Add, e1, e2);
    }
    public static NAryExpr Sub(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Sub, e1, e2);
    }
    public static NAryExpr Mul(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Mul, e1, e2);
    }
    public static NAryExpr Div(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Div, e1, e2);
    }
    public static NAryExpr Mod(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Mod, e1, e2);
    }
    public static NAryExpr RealDiv(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.RealDiv, e1, e2);
    }
    public static NAryExpr Pow(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Pow, e1, e2);
    }
    public static NAryExpr Subtype(Expr e1, Expr e2) {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Subtype, e1, e2);
    }

    public static IdentifierExpr Ident(string name, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
      return new IdentifierExpr(Token.NoToken, name, type);
    }

    public static IdentifierExpr Ident(Variable decl) {
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
      IdentifierExpr result = new IdentifierExpr(Token.NoToken, decl);
      return result;
    }

    public static LiteralExpr Literal(bool value) {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }
    public static LiteralExpr Literal(int value) {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, BigNum.FromInt(value));
    }
    public static LiteralExpr Literal(BigNum value) {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }
    public static LiteralExpr Literal(BigDec value) {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }

    private static LiteralExpr/*!*/ true_ = Literal(true);
    public static LiteralExpr/*!*/ True {
      get {
        Contract.Ensures(Contract.Result<LiteralExpr>() != null);
        return true_;
      }
    }

    private static LiteralExpr/*!*/ false_ = Literal(false);
    public static LiteralExpr/*!*/ False {
      get {
        Contract.Ensures(Contract.Result<LiteralExpr>() != null);
        return false_;
      }
    }


    public static NAryExpr Select(Expr map, params Expr[] args) {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return SelectTok(Token.NoToken, map, args);
    }

    public static NAryExpr Select(Expr map, List<Expr/*!*/>/*!*/ args) {
      Contract.Requires(map != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Select(map, args.ToArray());
    }

    // use a different name for this variant of the method
    // (-> some bug prevents overloading in this case)
    public static NAryExpr SelectTok(IToken x, Expr map, params Expr[] args) {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      List<Expr>/*!*/ allArgs = new List<Expr>();
      allArgs.Add(map);
      foreach (Expr/*!*/ a in args) {
        Contract.Assert(a != null);
        allArgs.Add(a);
      }
      return new NAryExpr(x, new MapSelect(Token.NoToken, args.Length), allArgs);
    }

    public static NAryExpr Store(Expr map, params Expr[] args) {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return StoreTok(Token.NoToken, map, args);
    }

    public static NAryExpr Store(Expr map, List<Expr/*!*/>/*!*/ indexes, Expr rhs) {
      Contract.Requires(rhs != null);
      Contract.Requires(map != null);
      Contract.Requires(cce.NonNullElements(indexes));
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      Expr[]/*!*/ allArgs = new Expr[indexes.Count + 1];
      for (int i = 0; i < indexes.Count; ++i)
        allArgs[i] = indexes[i];
      allArgs[indexes.Count] = rhs;
      return Store(map, allArgs);
    }

    // use a different name for this variant of the method
    // (-> some bug prevents overloading in this case)
    public static NAryExpr/*!*/ StoreTok(IToken x, Expr map, params Expr[] args) {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Requires(x != null);
      Contract.Requires(args.Length > 0);    // zero or more indices, plus the value
      Contract.Ensures(Contract.Result<NAryExpr>() != null);

      List<Expr>/*!*/ allArgs = new List<Expr>();
      allArgs.Add(map);
      foreach (Expr/*!*/ a in args) {
        Contract.Assert(a != null);
        allArgs.Add(a);
      }
      return new NAryExpr(x, new MapStore(Token.NoToken, args.Length - 1), allArgs);
    }

    public static NAryExpr CoerceType(IToken x, Expr subexpr, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(subexpr != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      List<Expr>/*!*/ args = new List<Expr>();
      args.Add(subexpr);
      return new NAryExpr(x, new TypeCoercion(x, type), args);
    }

    public static Expr BinaryTreeAnd(List<Expr> terms)
    {
        return BinaryTreeAnd(terms, 0, terms.Count - 1);
    }

    private static Expr BinaryTreeAnd(List<Expr> terms, int start, int end)
    {
        if (start > end)
            return Expr.True;
        if (start == end)
            return terms[start];
        if (start + 1 == end)
            return Expr.And(terms[start], terms[start + 1]);
        var mid = (start + end) / 2;
        return Expr.And(BinaryTreeAnd(terms, start, mid), BinaryTreeAnd(terms, mid + 1, end));
    }
  }
  [ContractClassFor(typeof(Expr))]
  public abstract class ExprContracts : Expr {
    public ExprContracts() :base(null, /*immutable=*/ false){

    }
    public override void Emit(TokenTextWriter wr, int contextBindingStrength, bool fragileContext) {
      Contract.Requires(wr != null);
      throw new NotImplementedException();
    }
    public override void ComputeFreeVariables(Set freeVars) {
      Contract.Requires(freeVars != null);
      throw new NotImplementedException();
    }
    public override Type ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        throw new NotImplementedException();
      }
    }
  }

  public class LiteralExpr : Expr {
    public readonly object/*!*/ Val;  // false, true, a BigNum, a BigDec, or a BvConst
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Val != null);
    }

    /// <summary>
    /// Creates a literal expression for the boolean value "b".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="b"></param>
    public LiteralExpr(IToken/*!*/ tok, bool b, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Val = b;
      Type = Type.Bool;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    /// <summary>
    /// Creates a literal expression for the integer value "v".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="v"></param>
    public LiteralExpr(IToken/*!*/ tok, BigNum v, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Val = v;
      Type = Type.Int;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    /// <summary>
    /// Creates a literal expression for the real value "v".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="v"></param>
    public LiteralExpr(IToken/*!*/ tok, BigDec v, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Val = v;
      Type = Type.Real;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    /// <summary>
    /// Creates a literal expression for the bitvector value "v".
    /// </summary>
    public LiteralExpr(IToken/*!*/ tok, BigNum v, int b, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= b);
      Val = new BvConst(v, b);
      Type = Type.GetBvType(b);
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is LiteralExpr))
        return false;

      LiteralExpr other = (LiteralExpr)obj;
      return object.Equals(this.Val, other.Val);
    }

    [Pure]
    public override int GetHashCode() {
      if (Immutable)
        return this.CachedHashCode;
      else
        return ComputeHashCode();
    }

    [Pure]
    public override int ComputeHashCode() {
      return this.Val.GetHashCode();
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      if (this.Val is bool) {
        stream.Write((bool)this.Val ? "true" : "false"); // correct capitalization
      } else {
        stream.Write(cce.NonNull(this.Val.ToString()));
      }
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      // nothing to resolve
    }
    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      // no free variables to add
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      this.Type = ShallowType;
    }

    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        if (Val is bool) {
          return Type.Bool;
        } else if (Val is BigNum) {
          return Type.Int;
        } else if (Val is BigDec) {
          return Type.Real;
        } else if (Val is BvConst) {
          return Type.GetBvType(((BvConst)Val).Bits);
        } else {
          {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          } // like, where did this value come from?!
        }
      }
    }

    public bool IsFalse {
      get {
        return Val is bool && ((bool)Val) == false;
      }
    }
    public bool IsTrue {
      get {
        return Val is bool && ((bool)Val) == true;
      }
    }

    // should be eliminated after converting everything to BigNums
    private int asInt {
      get {
        return asBigNum.ToIntSafe;
      }
    }

    public bool isBigNum {
      get {
        return Val is BigNum;
      }
    }

    public BigNum asBigNum {
      get {
        Contract.Assert(isBigNum);
        return (BigNum)cce.NonNull(Val);
      }
    }

    public bool isBigDec {
      get {
        return Val is BigDec;
      }
    }

    public BigDec asBigDec {
      get {
        Contract.Assert(isBigDec);
        return (BigDec)cce.NonNull(Val);
      }
    }

    public bool isBool {
      get {
        return Val is bool;
      }
    }

    public bool asBool {
      get {
        Contract.Assert(isBool);
        return (bool)cce.NonNull(Val);
      }
    }

    public bool isBvConst {
      get {
        return Val is BvConst;
      }
    }

    public BvConst asBvConst {
      get {
        Contract.Assert(isBvConst);
        return (BvConst)cce.NonNull(Val);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitLiteralExpr(this);
    }
  }

  public class BvConst {
    public readonly BigNum Value;
    public readonly int Bits;

    public BvConst(BigNum v, int b) {
      Contract.Assert(v.Signum >= 0);
      Value = v;
      Bits = b;
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return Value + "bv" + Bits;
    }

    [Pure]
    public string ToReadableString() {
      Contract.Ensures(Contract.Result<string>() != null);
      if (Value > BigNum.FromInt(10000)) {
        string val = cce.NonNull(Value.ToString("x"));
        int pos = val.Length % 4;
        string res = "0x" + val.Substring(0, pos);
        Contract.Assert(res != null);
        while (pos < val.Length) {
          res += "." + val.Substring(pos, 4);
          pos += 4;
        }
        return res + ".bv" + Bits;
      } else
        return ToString();
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      BvConst other = obj as BvConst;
      if (other == null)
        return false;

      return Bits == other.Bits && Value == other.Value;
    }

    [Pure]
    public override int GetHashCode() {
      unchecked {
        return Value.GetHashCode() ^ Bits;
      }
    }
  }

  public class IdentifierExpr : Expr {
    private string _Name;
    public string Name { // identifier symbol
      get {
        return _Name;
      }
      set {
        if (Immutable)
          throw new InvalidOperationException("Cannot change Name on Immutable Expr");
        
        _Name = value;
      }
    }
    private Variable _Decl;
    public Variable Decl {   // identifier declaration
      get {
        return _Decl;
      }
      set {
        if (Immutable)
          throw new InvalidOperationException("Cannot change Decl on Immutable Expr");

        _Decl = value;
      }
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
    }


    /// <summary>
    /// Creates an unresolved identifier expression.  This constructor is intended to be called
    /// only from within the parser; for use inside the translation, use another constructor, which
    /// specifies the type of the expression.
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="name"></param>
    internal IdentifierExpr(IToken/*!*/ tok, string/*!*/ name, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      _Name = name;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }
    /// <summary>
    /// Creates an unresolved identifier expression.
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="name"></param>
    /// <param name="type"></param>
    public IdentifierExpr(IToken/*!*/ tok, string/*!*/ name, Type/*!*/ type, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      _Name = name;
      Type = type;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    /// <summary>
    /// Creates a resolved identifier expression.
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="d"></param>
    public IdentifierExpr(IToken/*!*/ tok, Variable/*!*/ d, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(d != null);
      _Name = cce.NonNull(d.Name);
      _Decl = d;
      Type = d.TypedIdent.Type;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is IdentifierExpr))
        return false;

      IdentifierExpr other = (IdentifierExpr)obj;
      return object.Equals(this.Name, other.Name) && object.Equals(this.Decl, other.Decl);
    }

    [Pure]
    public override int GetHashCode() {
      if (Immutable)
        return this.CachedHashCode;
      else
        return ComputeHashCode();
    }

    [Pure]
    public override int ComputeHashCode() {
      int h = this.Name == null ? 0 : this.Name.GetHashCode();
      h ^= this.Decl == null ? 0 : this.Decl.GetHashCode();
      return h;
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds && !stream.UseForComputingChecksums) {
        stream.Write("{0}^^", this.Decl == null ? "NoDecl" : "h" + this.Decl.GetHashCode());
      }
      stream.Write(this, "{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      if (Decl != null) {
        // already resolved, but re-resolve type just in case it came from an unresolved type
        if (Type != null) {
          Type = Type.ResolveType(rc);
        }
        return;
      }
      Decl = rc.LookUpVariable(Name);
      if (Decl == null) {
        rc.Error(this, "undeclared identifier: {0}", Name);
      } else if (rc.StateMode == ResolutionContext.State.StateLess && Decl is GlobalVariable) {
        rc.Error(this, "cannot refer to a global variable in this context: {0}", Name);
      }
      if (Type != null) {
        Type = Type.ResolveType(rc);
      }
    }
    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      Contract.Assume(this.Decl != null);
      freeVars.Add(Decl);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      if (this.Decl != null) {
        // sanity check
        if (Type != null && !Type.Equals(Decl.TypedIdent.Type)) {
          tc.Error(this, "internal error, shallow-type assignment was done incorrectly, {0}:{1} != {2}",
                         Name, Type, Decl.TypedIdent.Type);
          {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          }
        }
        Type = Decl.TypedIdent.Type;
      }
    }

    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        Contract.Assert(Type != null);
        return Type;
      }
    }

    public sealed class ConstantFunApp {
      private IdentifierExpr/*!*/ identifierExpr;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(identifierExpr != null);
        Contract.Invariant(emptyArgs != null);
      }

      public IdentifierExpr/*!*/ IdentifierExpr {
        get {
          Contract.Requires(IdentifierExpr != null);
          return identifierExpr;
        }
      }

      private static IList/*!*/ emptyArgs = ArrayList.ReadOnly(cce.NonNull((IList/*!*/)new ArrayList()));
      public IList/*!*/ Arguments {
        get {
          Contract.Ensures(Contract.Result<IList>() != null);
          return emptyArgs;
        }
      }

      public ConstantFunApp(IdentifierExpr ie, Constant c) {
        Contract.Requires(c != null);
        Contract.Requires(ie != null);
        this.identifierExpr = ie;
      }

    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitIdentifierExpr(this);
    }
  }

  public class OldExpr : Expr
  {
    private Expr _Expr;
    public Expr/*!*/ Expr {
      get {
        return _Expr;
      }
      set {
        if (Immutable)
          throw new InvalidOperationException("Cannot change Expr of an Immutable OldExpr");

        _Expr = value;
      }
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public OldExpr(IToken/*!*/ tok, Expr/*!*/ expr, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      _Expr = expr;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is OldExpr))
        return false;

      OldExpr other = (OldExpr)obj;
      return object.Equals(this.Expr, other.Expr);
    }
    [Pure]
    public override int GetHashCode() {
      if (Immutable)
        return this.CachedHashCode;
      else
        return ComputeHashCode ();
    }
    public override int ComputeHashCode() {
      // FIXME: This is wrong, it's as if the OldExpr node isn't there at all
      return this.Expr == null ? 0 : this.Expr.GetHashCode();
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      stream.Write(this, "old(");
      this.Expr.Emit(stream);
      stream.Write(")");
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      if (rc.StateMode != ResolutionContext.State.Two) {
        rc.Error(this, "old expressions allowed only in two-state contexts");
      }
      Expr.Resolve(rc);
    }
    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      Expr.ComputeFreeVariables(freeVars);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      Expr.Typecheck(tc);
      Type = Expr.Type;
    }
    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Expr.ShallowType;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitOldExpr(this);
    }
  }
  [ContractClass(typeof(IAppliableVisitorContracts<>))]
  public interface IAppliableVisitor<T> {
    T Visit(UnaryOperator/*!*/ unaryOperator);
    T Visit(BinaryOperator/*!*/ binaryOperator);
    T Visit(FunctionCall/*!*/ functionCall);
    T Visit(MapSelect/*!*/ mapSelect);
    T Visit(MapStore/*!*/ mapStore);
    T Visit(TypeCoercion/*!*/ typeCoercion);
    T Visit(ArithmeticCoercion/*!*/ arithCoercion);
    T Visit(IfThenElse/*!*/ ifThenElse);
  }
  [ContractClassFor(typeof(IAppliableVisitor<>))]
  public abstract class IAppliableVisitorContracts<T> : IAppliableVisitor<T> {

    #region IAppliableVisitor<T> Members

    public T Visit(UnaryOperator unaryOperator) {
      Contract.Requires(unaryOperator != null);
      throw new NotImplementedException();
    }

    public T Visit(BinaryOperator binaryOperator) {
      Contract.Requires(binaryOperator != null);
      throw new NotImplementedException();
    }

    public T Visit(FunctionCall functionCall) {
      Contract.Requires(functionCall != null);
      throw new NotImplementedException();
    }

    public T Visit(MapSelect mapSelect) {
      Contract.Requires(mapSelect != null);
      throw new NotImplementedException();
    }

    public T Visit(MapStore mapStore) {
      Contract.Requires(mapStore != null);
      throw new NotImplementedException();
    }

    public T Visit(TypeCoercion typeCoercion) {
      Contract.Requires(typeCoercion != null);
      throw new NotImplementedException();
    }

    public T Visit(ArithmeticCoercion arithCoercion) {
      Contract.Requires(arithCoercion != null);
      throw new NotImplementedException();
    }

    public T Visit(IfThenElse ifThenElse) {
      Contract.Requires(ifThenElse != null);
      throw new NotImplementedException();
    }

    #endregion
  }

  [ContractClass(typeof(IAppliableContracts))]
  public interface IAppliable {
    string/*!*/ FunctionName {
      get;
    }

    /// <summary>
    /// Emits to "stream" the operator applied to the given arguments.
    /// The length of "args" can be anything that the parser allows for this appliable operator
    /// (but can be nothing else).
    /// </summary>
    /// <param name="args"></param>
    /// <param name="stream"></param>
    /// <param name="contextBindingStrength"></param>
    /// <param name="fragileContext"></param>
    void Emit(IList<Expr>/*!*/ args, TokenTextWriter/*!*/ stream, int contextBindingStrength, bool fragileContext);

    void Resolve(ResolutionContext/*!*/ rc, Expr/*!*/ subjectForErrorReporting);

    /// <summary>
    /// Requires the object to have been properly resolved.
    /// </summary>
    int ArgumentCount {
      get;
    }

    /// <summary>
    /// Typechecks the arguments "args" for the Appliable.  If the arguments are
    /// appropriate, returns the result type; otherwise returns null.
    /// As result of the type checking, the values of type parameters of the
    /// appliable can be returned (which are then stored in the NAryExpr and later
    /// also used in the VCExprAST).
    /// Requires the object to have been successfully resolved.
    /// Requires args.Length == ArgumentCount.
    /// Requires all elements of "args" to have a non-null Type field.
    /// </summary>
    /// <param name="args"></param>
    /// <param name="tc"></param>
    Type Typecheck(ref List<Expr>/*!*/ args, out TypeParamInstantiation/*!*/ tpInstantiation, TypecheckingContext/*!*/ tc);

    // Contract.Requires( Microsoft.SpecSharp.Collections.Reductions.Forall{Expr! arg in args; arg.Type != null});

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    Type/*!*/ ShallowType(IList<Expr>/*!*/ args);

    T Dispatch<T>(IAppliableVisitor<T>/*!*/ visitor);
  }
  [ContractClassFor(typeof(IAppliable))]
  abstract class IAppliableContracts : IAppliable {

    #region IAppliable Members

    public string FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();
      }
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      Contract.Requires(args != null);
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      Contract.Requires(rc != null);
      Contract.Requires(subjectForErrorReporting != null);
      throw new NotImplementedException();
    }

    public int ArgumentCount {
      get {
        throw new NotImplementedException();
      }
    }

    public Type Typecheck(ref List<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc) {
      Contract.Requires(args != null);
      Contract.Requires(tc != null);
      Contract.Ensures(Contract.ValueAtReturn(out args) != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(args.Count == Contract.OldValue(args.Count));
      throw new NotImplementedException();
    }

    public Type ShallowType(IList<Expr> args) {
      Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor) {
      Contract.Requires(visitor != null);
      throw new NotImplementedException();
    }

    #endregion
  }


  [ContractClass(typeof(IOverloadedAppliableContracts))]
  public interface IOverloadedAppliable {
    void ResolveOverloading(NAryExpr/*!*/ expr);
    bool DoNotResolveOverloading { get; set; }
  }
  [ContractClassFor(typeof(IOverloadedAppliable))]
  public abstract class IOverloadedAppliableContracts : IOverloadedAppliable {

    #region IOverloadedAppliable Members

    void IOverloadedAppliable.ResolveOverloading(NAryExpr expr) {
      Contract.Requires(expr != null);
      throw new NotImplementedException();
    }

    public bool DoNotResolveOverloading
    {
      get
      {
        throw new NotImplementedException();
      }
      set
      {
        throw new NotImplementedException();
      }
    }

    #endregion
  }

  public class UnaryOperator : IAppliable {
    private IToken/*!*/ tok;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }

    public enum Opcode {
      Neg,
      Not
    };
    private Opcode op;
    public Opcode Op {
      get {
        return op;
      }
    }
    public UnaryOperator(IToken tok, Opcode op) {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.op = op;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is UnaryOperator))
        return false;

      UnaryOperator other = (UnaryOperator)obj;
      return object.Equals(this.op, other.op);
    }
    [Pure]
    public override int GetHashCode() {
      return (int)this.op;
    }

    public string/*!*/ FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);

        switch (this.op) {
          case Opcode.Neg:
            return "-";
          case Opcode.Not:
            return "!";
        }
        System.Diagnostics.Debug.Fail("unknown unary operator: " + op.ToString());
        throw new Exception();
      }
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.SetToken(ref this.tok);
      Contract.Assert(args.Count == 1);
      // determine if parens are needed
      int opBindingStrength = 0x70;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
        (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded) {
        stream.Write("(");
      }
      stream.Write(FunctionName);
      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      if (parensNeeded) {
        stream.Write(")");
      }
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      if (rc.TriggerMode && this.op == Opcode.Not) {
        rc.Error(subjectForErrorReporting, "boolean operators are not allowed in triggers");
      }
    }

    public int ArgumentCount {
      get {
        return 1;
      }
    }

    public Type Typecheck(ref List<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(Contract.ValueAtReturn(out args) != null);

      Contract.Assume(args.Count == 1);
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      Type arg0type = cce.NonNull(cce.NonNull(args[0]).Type);
      switch (this.op) {
        case Opcode.Neg:
          if (arg0type.Unify(Type.Int)) {
            return Type.Int;
          }
          if (arg0type.Unify(Type.Real)) {
            return Type.Real;
          }
          goto BAD_TYPE;
        case Opcode.Not:
          if (arg0type.Unify(Type.Bool)) {
            return Type.Bool;
          }
          goto BAD_TYPE;
      }
      System.Diagnostics.Debug.Fail("unknown unary operator: " + op.ToString());
      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    BAD_TYPE:
      tc.Error(this.tok, "invalid argument type ({1}) to unary operator {0}",
        this.FunctionName, arg0type);
      return null;
    }
    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      switch (this.op) {
        case Opcode.Neg:
          return cce.NonNull(cce.NonNull(args[0]).Type);
        case Opcode.Not:
          return Type.Bool;
        default: {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          } // unexpected unary operator
      }
    }

    public object Evaluate(object argument) {
      if (argument == null) {
        return null;
      }
      switch (this.op) {
        case Opcode.Neg:
          if (argument is BigNum) {
            return -((BigNum)argument);
          }
          if (argument is BigDec) {
            return -((BigDec)argument);
          }
          break;
        case Opcode.Not:
          if (argument is bool) {
            return !((bool)argument);
          }
          throw new System.InvalidOperationException("unary Not only applies to bool");
      }
      return null; // unreachable
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class BinaryOperator : IAppliable, IOverloadedAppliable {
    private IToken/*!*/ tok;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }

    public bool DoNotResolveOverloading { get; set; }

    public enum Opcode {
      Add,
      Sub,
      Mul,
      Div,
      Mod,
      RealDiv,
      Pow,
      Eq,
      Neq,
      Gt,
      Ge,
      Lt,
      Le,
      And,
      Or,
      Imp,
      Iff,
      Subtype
    };
    private Opcode op;
    public Opcode Op {
      get {
        return op;
      }
    }
    public BinaryOperator(IToken tok, Opcode op) {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.op = op;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is BinaryOperator))
        return false;

      BinaryOperator other = (BinaryOperator)obj;
      return object.Equals(this.op, other.op);
    }

    [Pure]
    public override int GetHashCode() {
      return (int)this.op << 1;
    }

    public string/*!*/ FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);

        switch (this.op) {
          case Opcode.Add:
            return "+";
          case Opcode.Sub:
            return "-";
          case Opcode.Mul:
            return "*";
          case Opcode.Div:
            return "div";
          case Opcode.Mod:
            return "mod";
          case Opcode.RealDiv:
            return "/";
          case Opcode.Pow:
            return "**";
          case Opcode.Eq:
            return "==";
          case Opcode.Neq:
            return "!=";
          case Opcode.Gt:
            return ">";
          case Opcode.Ge:
            return ">=";
          case Opcode.Lt:
            return "<";
          case Opcode.Le:
            return "<=";
          case Opcode.And:
            return "&&";
          case Opcode.Or:
            return "||";
          case Opcode.Imp:
            return "==>";
          case Opcode.Iff:
            return "<==>";
          case Opcode.Subtype:
            return "<:";
        }
        System.Diagnostics.Debug.Fail("unknown binary operator: " + op.ToString());
        throw new Exception();
      }
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.SetToken(ref this.tok);
      Contract.Assert(args.Count == 2);
      // determine if parens are needed
      int opBindingStrength;
      bool fragileLeftContext = false;  // false means "allow same binding power on left without parens"
      bool fragileRightContext = false;  // false means "allow same binding power on right without parens"
      switch (this.op) {
        case Opcode.Add:
          opBindingStrength = 0x40;
          break;
        case Opcode.Sub:
          opBindingStrength = 0x40;
          fragileRightContext = true;
          break;
        case Opcode.Mul:
          opBindingStrength = 0x50;
          break;
        case Opcode.Div:
          opBindingStrength = 0x50;
          fragileRightContext = true;
          break;
        case Opcode.Mod:
          opBindingStrength = 0x50;
          fragileRightContext = true;
          break;
        case Opcode.RealDiv:
          opBindingStrength = 0x50;
          fragileRightContext = true;
          break;
        case Opcode.Pow:
          opBindingStrength = 0x60;
          fragileRightContext = true;
          break;
        case Opcode.Eq:
        case Opcode.Neq:
        case Opcode.Gt:
        case Opcode.Ge:
        case Opcode.Lt:
        case Opcode.Le:
        case Opcode.Subtype:
          opBindingStrength = 0x30;
          fragileLeftContext = fragileRightContext = true;
          break;
        case Opcode.And:
          opBindingStrength = 0x20;
          break;
        case Opcode.Or:
          opBindingStrength = 0x21;
          break;
        case Opcode.Imp:
          opBindingStrength = 0x10;
          fragileLeftContext = true;
          break;
        case Opcode.Iff:
          opBindingStrength = 0x00;
          break;
        default:
          System.Diagnostics.Debug.Fail("unknown binary operator: " + op.ToString());
          opBindingStrength = -1;  // to please compiler, which refuses to consider whether or not all enumeration cases have been considered!
          break;
      }
      int opBS = opBindingStrength & 0xF0;
      int ctxtBS = contextBindingStrength & 0xF0;
      bool parensNeeded = opBS < ctxtBS ||
        (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

      var pop = stream.push(FunctionName);
      if (parensNeeded) {
        stream.Write("(");
      }
      cce.NonNull(args[0]).Emit(stream, opBindingStrength, fragileLeftContext);
      stream.sep();
      stream.Write(" {0} ", FunctionName);
      cce.NonNull(args[1]).Emit(stream, opBindingStrength, fragileRightContext);
      if (parensNeeded) {
        stream.Write(")");
      }
      stream.pop(pop);
    }
    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      if (rc.TriggerMode) {
        switch (this.op) {
          case Opcode.Add:
          case Opcode.Sub:
          case Opcode.Mul:
          case Opcode.Div:
          case Opcode.Mod:
          case Opcode.RealDiv:
          case Opcode.Pow:
          case Opcode.Neq:  // Neq is allowed, but not Eq
          case Opcode.Subtype:
            // These are fine
            break;

          case Opcode.Eq:
            rc.Error(subjectForErrorReporting, "equality is not allowed in triggers");
            break;

          case Opcode.Gt:
          case Opcode.Ge:
          case Opcode.Lt:
          case Opcode.Le:
            rc.Error(subjectForErrorReporting, "arithmetic comparisons are not allowed in triggers");
            break;

          case Opcode.And:
          case Opcode.Or:
          case Opcode.Imp:
          case Opcode.Iff:
            rc.Error(subjectForErrorReporting, "boolean operators are not allowed in triggers");
            break;

          default:
            System.Diagnostics.Debug.Fail("unknown binary operator: " + this.op.ToString());
            break;
        }
      }
    }
    public int ArgumentCount {
      get {
        return 2;
      }
    }
    public Type Typecheck(ref List<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(args != null);
      Contract.Assert(args.Count == 2);
      // the default; the only binary operator with a type parameter is equality, but right
      // we don't store this parameter because it does not appear necessary
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      Expr arg0 = cce.NonNull(args[0]);
      Expr arg1 = cce.NonNull(args[1]);
      Type arg0type = cce.NonNull(arg0.Type);
      Type arg1type = cce.NonNull(arg1.Type);
      switch (this.op) {
        case Opcode.Add:
        case Opcode.Sub:
        case Opcode.Mul:
          if (arg0type.Unify(Type.Int) && arg1type.Unify(Type.Int)) {
            return Type.Int;
          }
          if (arg0type.Unify(Type.Real) && arg1type.Unify(Type.Real)) {
            return Type.Real;
          }
          goto BAD_TYPE;
        case Opcode.Div:
        case Opcode.Mod:
          if (arg0type.Unify(Type.Int) && arg1type.Unify(Type.Int)) {
            return Type.Int;
          }
          goto BAD_TYPE;
        case Opcode.RealDiv:
          if ((arg0type.Unify(Type.Int) || arg0type.Unify(Type.Real)) &&
              (arg1type.Unify(Type.Int) || arg1type.Unify(Type.Real))) {
            return Type.Real;
          }
          goto BAD_TYPE;
        case Opcode.Pow:
          if (arg0type.Unify(Type.Real) && arg1type.Unify(Type.Real)) {
            return Type.Real;
          }
          goto BAD_TYPE;
        case Opcode.Eq:
        case Opcode.Neq:
          // Comparison is allowed if the argument types are unifiable
          // (i.e., if there is any chance that the values of the arguments are 
          // in the same domain)
          if (arg0type.Equals(arg1type)) {
            // quick path
            return Type.Bool;
          }
          List<TypeVariable>/*!*/ unifiable = new List<TypeVariable>();
          unifiable.AddRange(arg0type.FreeVariables);
          unifiable.AddRange(arg1type.FreeVariables);

          if (arg0type.Unify(arg1type, unifiable, new Dictionary<TypeVariable/*!*/, Type/*!*/>()))
            return Type.Bool;
          goto BAD_TYPE;
        case Opcode.Gt:
        case Opcode.Ge:
        case Opcode.Lt:
        case Opcode.Le:
          if (arg0type.Unify(Type.Int) && arg1type.Unify(Type.Int)) {
            return Type.Bool;
          }
          if (arg0type.Unify(Type.Real) && arg1type.Unify(Type.Real)) {
            return Type.Bool;
          }
          goto BAD_TYPE;
        case Opcode.And:
        case Opcode.Or:
        case Opcode.Imp:
        case Opcode.Iff:
          if (arg0type.Unify(Type.Bool) && arg1type.Unify(Type.Bool)) {
            return Type.Bool;
          }
          goto BAD_TYPE;
        case Opcode.Subtype:
          // Subtype is polymorphically typed and can compare things of
          // arbitrary types (but both arguments must have the same type)
          if (arg0type.Unify(arg1type)) {
            return Type.Bool;
          }
          goto BAD_TYPE;
      }
      System.Diagnostics.Debug.Fail("unknown binary operator: " + op.ToString());
      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    BAD_TYPE:
      tc.Error(this.tok, "invalid argument types ({1} and {2}) to binary operator {0}", this.FunctionName, arg0type, arg1type);
      return null;
    }

    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      switch (this.op) {
        case Opcode.Add:
        case Opcode.Sub:
        case Opcode.Mul:
          return cce.NonNull(args[0]).ShallowType;

        case Opcode.Div:
        case Opcode.Mod:
          return Type.Int;

        case Opcode.RealDiv:
        case Opcode.Pow:
          return Type.Real;

        case Opcode.Eq:
        case Opcode.Neq:
        case Opcode.Gt:
        case Opcode.Ge:
        case Opcode.Lt:
        case Opcode.Le:
        case Opcode.And:
        case Opcode.Or:
        case Opcode.Imp:
        case Opcode.Iff:
        case Opcode.Subtype:
          return Type.Bool;

        default: {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          } // unexpected binary operator
      }
    }

    public void ResolveOverloading(NAryExpr expr) {
      //Contract.Requires(expr != null);

      // immutable Expr must not be modified
      if (DoNotResolveOverloading || expr.Immutable)
      {
        return;
      }

      Expr arg0 = cce.NonNull(expr.Args[0]);
      Expr arg1 = cce.NonNull(expr.Args[1]);
      switch (op) {
        case Opcode.Eq:
          if (arg0.Type != null && arg0.Type.IsBool && arg1.Type != null && arg1.Type.IsBool) {
            expr.Fun = new BinaryOperator(tok, Opcode.Iff);
          }
          break;
        case Opcode.Neq:
          if (arg0.Type != null && arg0.Type.IsBool && arg1.Type != null && arg1.Type.IsBool) {
            expr.Fun = new BinaryOperator(tok, Opcode.Iff);
            var arg1New = new NAryExpr(expr.tok, new UnaryOperator(tok, UnaryOperator.Opcode.Not), new List<Expr> { arg1 });

            // ugly ... there should be some more general approach,
            // e.g., to typecheck the whole expression again
            arg1New.Type = Type.Bool;
            arg1New.TypeParameters = SimpleTypeParamInstantiation.EMPTY;

            expr.Args[1] = arg1New;
          }
          break;
      }
    }

    public object Evaluate(object e1, object e2) {
      if (e1 == null || e2 == null) {
        return null;
      }

      switch (this.op) {
        case Opcode.Add:
          if (e1 is BigNum && e2 is BigNum) {
            return ((BigNum)e1) + ((BigNum)e2);
          }
          if (e1 is BigDec && e2 is BigDec) {
            return ((BigDec)e1) + ((BigDec)e2);
          }
          break;
        case Opcode.Sub:
          if (e1 is BigNum && e2 is BigNum) {
            return ((BigNum)e1) - ((BigNum)e2);
          }
          if (e1 is BigDec && e2 is BigDec) {
            return ((BigDec)e1) - ((BigDec)e2);
          }
          break;
        case Opcode.Mul:
          if (e1 is BigNum && e2 is BigNum) {
            return ((BigNum)e1) * ((BigNum)e2);
          }
          if (e1 is BigDec && e2 is BigDec) {
            return ((BigDec)e1) * ((BigDec)e2);
          }
          break;
        case Opcode.Div:
          if (e1 is BigNum && e2 is BigNum) {
            return /* TODO: right semantics? */ ((BigNum)e1) / ((BigNum)e2);
          }
          break;
        case Opcode.Mod:
          if (e1 is BigNum && e2 is BigNum) {
            return /* TODO: right semantics? */ ((BigNum)e1) % ((BigNum)e2);
          }
          break;
        case Opcode.RealDiv:
          // TODO: add partial evaluation fro real division
          break;
        case Opcode.Pow:
          // TODO: add partial evaluation fro real exponentiation
          break;
        case Opcode.Lt:
          if (e1 is BigNum && e2 is BigNum) {
            return ((BigNum)e1) < ((BigNum)e2);
          }
          if (e1 is BigDec && e2 is BigDec) {
            return ((BigDec)e1) < ((BigDec)e2);
          }
          break;
        case Opcode.Le:
          if (e1 is BigNum && e2 is BigNum) {
            return ((BigNum)e1) <= ((BigNum)e2);
          }
          if (e1 is BigDec && e2 is BigDec) {
            return ((BigDec)e1) <= ((BigDec)e2);
          }
          break;
        case Opcode.Gt:
          if (e1 is BigNum && e2 is BigNum) {
            return ((BigNum)e1) > ((BigNum)e2);
          }
          if (e1 is BigDec && e2 is BigDec) {
            return ((BigDec)e1) > ((BigDec)e2);
          }
          break;
        case Opcode.Ge:
          if (e1 is BigNum && e2 is BigNum) {
            return ((BigNum)e1) >= ((BigNum)e2);
          }
          if (e1 is BigDec && e2 is BigDec) {
            return ((BigDec)e1) >= ((BigDec)e2);
          }
          break;

        case Opcode.And:
          if (e1 is bool && e2 is bool) {
            return (bool)e1 && (bool)e2;
          }
          break;
        case Opcode.Or:
          if (e1 is bool && e2 is bool) {
            return (bool)e1 || (bool)e2;
          }
          break;
        case Opcode.Imp:
          if (e1 is bool && e2 is bool) {
            return !(bool)e1 || (bool)e2;
          }
          break;
        case Opcode.Iff:
          if (e1 is bool && e2 is bool) {
            return e1 == e2;
          }
          break;

        case Opcode.Eq:
          return Equals(e1, e2);
        case Opcode.Neq:
          return !Equals(e1, e2);

        case Opcode.Subtype:
          throw new System.NotImplementedException();
      }
      throw new System.InvalidOperationException("bad types to binary operator " + this.op);
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }

  }

  public class FunctionCall : IAppliable {
    private IdentifierExpr/*!*/ name;
    public Function Func;
    public FunctionCall(IdentifierExpr name) {
      Contract.Requires(name != null);
      this.name = name;
    }
    public FunctionCall(Function f) {
      Contract.Requires(f != null);
      this.Func = f;
      this.name = new IdentifierExpr(Token.NoToken, f.Name);

      // We need set the type of this IdentifierExpr so ShallowType() works
      Debug.Assert(f.OutParams.Count > 0);
      this.name.Type = f.OutParams[0].TypedIdent.Type;
    }
    public string/*!*/ FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return this.name.Name;
      }
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
    }
    
    public FunctionCall createUnresolvedCopy()
    {
        return new FunctionCall(new IdentifierExpr(name.tok, name.Name, name.Type));
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return name.Name;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object other) {
      FunctionCall fc = other as FunctionCall;
      return fc != null && this.Func == fc.Func;
    }
    [Pure]
    public override int GetHashCode() {
      Contract.Assume(this.Func != null);
      return Func.GetHashCode();
    }

    virtual public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      this.name.Emit(stream, 0xF0, false);
      if (stream.UseForComputingChecksums)
      {
        var c = Func.DependencyChecksum;
        if (c != null)
        {
          stream.Write(string.Format("[dependency_checksum:{0}]", c));
        }
      }
      stream.Write("(");
      args.Emit(stream);
      stream.Write(")");
    }
    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      if (Func != null) {
        // already resolved
        return;
      }
      Func = rc.LookUpProcedure(name.Name) as Function;
      if (Func == null) {
        rc.Error(this.name, "use of undeclared function: {0}", name.Name);
      }
      else if (name.Type == null) {
        // We need set the type of this IdentifierExpr so ShallowType() works
        Debug.Assert(name.Type == null);
        Debug.Assert(Func.OutParams.Count > 0);
        name.Type = Func.OutParams[0].TypedIdent.Type;
      }
    }
    public virtual int ArgumentCount {
      get {
        Contract.Assume(Func != null);  // ArgumentCount requires object to be properly resolved.
        return Func.InParams.Count;
      }
    }
    public virtual Type Typecheck(ref List<Expr> actuals, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      //Contract.Requires(actuals != null);
      Contract.Ensures(Contract.ValueAtReturn(out actuals) != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Assume(this.Func != null);
      Contract.Assume(actuals.Count == Func.InParams.Count);
      Contract.Assume(Func.OutParams.Count == 1);

      List<Type/*!*/>/*!*/ resultingTypeArgs;
      List<Type> actualResultType =
        Type.CheckArgumentTypes(Func.TypeParameters,
                                out resultingTypeArgs,
                                new List<Type>(Func.InParams.Select(Item => Item.TypedIdent.Type).ToArray()),
                                actuals,
                                new List<Type>(Func.OutParams.Select(Item => Item.TypedIdent.Type).ToArray()),
                                null,
        // we need some token to report a possibly wrong number of
        // arguments
                                actuals.Count > 0 ? cce.NonNull(actuals[0]).tok : Token.NoToken,
                                "application of " + name.Name,
                                tc);

      if (actualResultType == null) {
        tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
        return null;
      } else {
        Contract.Assert(actualResultType.Count == 1);
        tpInstantiation =
          SimpleTypeParamInstantiation.From(Func.TypeParameters, resultingTypeArgs);
        return actualResultType[0];
      }
    }
    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assume(name.Type != null);
      return name.Type;
    }

    public virtual T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class TypeCoercion : IAppliable {
    private IToken/*!*/ tok;
    public Type/*!*/ Type;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }

    public TypeCoercion(IToken tok, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      this.tok = tok;
      this.Type = type;
    }

    public override bool Equals(object obj) {
      TypeCoercion other = obj as TypeCoercion;
      if (other == null) {
        return false;
      } else {
        return object.Equals(Type, other.Type);
      }
    }



    public
      string/*!*/ FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);

        return ":";
      }
    }

    public void Emit(IList<Expr>/*!*/ args, TokenTextWriter/*!*/ stream,
                     int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(args != null);
      //Contract.Requires(stream != null);
      stream.SetToken(ref this.tok);
      Contract.Assert(args.Count == 1);
      // determine if parens are needed
      int opBindingStrength = 0x80;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
        (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded)
        stream.Write("(");

      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      stream.Write("{0} ", FunctionName);
      Type.Emit(stream, 0);

      if (parensNeeded)
        stream.Write(")");
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      this.Type = this.Type.ResolveType(rc);
    }

    public int ArgumentCount {
      get {
        return 1;
      }
    }

    public Type Typecheck(ref List<Expr>/*!*/ args,
                          out TypeParamInstantiation/*!*/ tpInstantiation,
                          TypecheckingContext/*!*/ tc) {
      //Contract.Requires(args != null);
      //Contract.Requires(tc != null);
      Contract.Ensures(args != null);

      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);

      Contract.Assume(args.Count == 1);
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;

      if (!this.Type.Unify(cce.NonNull(cce.NonNull(args[0]).Type)))
        tc.Error(this.tok, "{0} cannot be coerced to {1}",
                 cce.NonNull(args[0]).Type, this.Type);
      return this.Type;
    }

    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.Type;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }

  }

  public class ArithmeticCoercion : IAppliable {
    public enum CoercionType {
      ToInt,
      ToReal
    }

    private IToken/*!*/ tok;
    public readonly CoercionType Coercion;
    private readonly string name;
    private readonly Type type;
    private readonly Type argType;
    private readonly int hashCode;

    public ArithmeticCoercion(IToken tok, CoercionType coercion) {
      this.tok = tok;
      this.Coercion = coercion;

      switch (coercion) {
        case CoercionType.ToInt:
          this.name = "int";
          this.type = Type.Int;
          this.argType = Type.Real;
          this.hashCode = 1;
          break;
        case CoercionType.ToReal:
          this.name = "real";
          this.type = Type.Real;
          this.argType = Type.Int;
          this.hashCode = 2;
          break;
        default:
          Contract.Assert(false);
          break;
      }
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return this.name;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object other) {
      ArithmeticCoercion ac = other as ArithmeticCoercion;
      return ac != null && this.Coercion == ac.Coercion;
    }

    [Pure]
    public override int GetHashCode() {
      return this.hashCode;
    }

    public string/*!*/ FunctionName {
      get {
        return this.name;
      }
    }

    public int ArgumentCount {
      get {
        return 1;
      }
    }

    virtual public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.Write(this.name);
      stream.Write("(");
      args.Emit(stream);
      stream.Write(")");
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
    }

    public virtual Type Typecheck(ref List<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);

      Contract.Assert(args.Count == 1);

      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;

      if (!cce.NonNull(cce.NonNull(args[0]).Type).Unify(argType)) {
        tc.Error(this.tok, "argument type {0} does not match expected type {1}", cce.NonNull(args[0]).Type, this.argType);
      }

      return this.type;
    }

    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.type;
    }

    public virtual T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class NAryExpr : Expr {
    [Additive]
    [Peer]
    private IAppliable _Fun;
    public IAppliable/*!*/ Fun {
      get {
        return _Fun;
      }
      set {
        if (Immutable)
          throw new InvalidOperationException("Cannot change Function used by Immutable NAryExpr");

        _Fun = value;
      }
    }
    private List<Expr> _Args;
    public IList<Expr> Args {
      get {
        if (Immutable)
          return _Args.AsReadOnly();
        else
          return _Args;
      }
      set {
        if (Immutable)
          throw new InvalidOperationException("Cannot change Args of Immutable NAryExpr");

        _Args = value as List<Expr>;
    }
  }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Fun != null);
      Contract.Invariant(Args != null);
    }


    // The instantiation of type parameters that is determined during type checking.
    // Which type parameters are available depends on the IAppliable
    public TypeParamInstantiation TypeParameters = null;

    [Captured]
    public NAryExpr(IToken/*!*/ tok, IAppliable/*!*/ fun, IList<Expr>/*!*/ args, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(fun != null);
      Contract.Requires(args != null);
      _Fun = fun;
      Contract.Assert(Contract.ForAll(0, args.Count, index => args[index] != null));
      if (immutable) {
          // We need to make a new list because the client might be holding
          // references to the list that they gave us which could be used to
          // circumvent the immutability enforcement
          _Args = new List<Expr>(args);
          CachedHashCode = ComputeHashCode();
      } else {
        if (args is List<Expr>) {
          // Preserve NAryExpr's old behaviour, we take ownership of the List<Expr>.
          // We can only do this if the type matches
          _Args = args as List<Expr>;
        }
        else {
          // Otherwise we must make a copy
          _Args = new List<Expr> (args);
        }
      }
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is NAryExpr))
        return false;

      NAryExpr other = (NAryExpr)obj;
      return object.Equals(this.Fun, other.Fun) && this.Args.SequenceEqual(other.Args);
    }
    
    [Pure]
    public override int GetHashCode() {
      if (Immutable)
        return this.CachedHashCode;
      else
        return ComputeHashCode();
    }

    [Pure]
    public override int ComputeHashCode() {
      int h = this.Fun.GetHashCode();
      // DO NOT USE Args.GetHashCode() because that uses Object.GetHashCode() which uses references
      // We want structural equality
      foreach (var arg in Args) {
        h = (97*h) + arg.GetHashCode();
      }
      return h;
    }
    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      Fun.Emit(Args, stream, contextBindingStrength, fragileContext);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      Fun.Resolve(rc, this);
      foreach (Expr/*!*/ e in Args) {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }
    }
    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      foreach (Expr/*!*/ e in Args) {
        Contract.Assert(e != null);
        e.ComputeFreeVariables(freeVars);
      }
      // also add the free type variables
      if (TypeParameters != null) {
        foreach (TypeVariable/*!*/ var in TypeParameters.FormalTypeParams) {
          Contract.Assert(var != null);
          foreach (TypeVariable/*!*/ w in TypeParameters[var].FreeVariables) {
            Contract.Assert(w != null);
            freeVars.Add(w);
          }
        }
      }
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      int prevErrorCount = tc.ErrorCount;
      foreach (Expr/*!*/ e in Args) {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }
      if (Fun.ArgumentCount != Args.Count) {
        tc.Error(this, "wrong number of arguments to function: {0} ({1} instead of {2})",
                 Fun.FunctionName, Args.Count, Fun.ArgumentCount);
      } else if (tc.ErrorCount == prevErrorCount &&
        // if the type parameters are set, this node has already been
        // typechecked and does not need to be checked again
               TypeParameters == null) {
        TypeParamInstantiation tpInsts;
        Type = Fun.Typecheck(ref _Args, out tpInsts, tc); // FIXME: Might break immutability
        TypeParameters = tpInsts;
      }
      IOverloadedAppliable oa = Fun as IOverloadedAppliable;
      if (oa != null) {
        oa.ResolveOverloading(this);
      }
      if (Type == null) {
        // set Type to some non-null value
        Type = new TypeProxy(this.tok, "type_checking_error");
      }
    }
    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Fun.ShallowType(Args);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitNAryExpr(this);
    }
  }

  public class MapSelect : IAppliable {

    public readonly int Arity;
    private readonly IToken/*!*/ tok;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }


    public MapSelect(IToken tok, int arity) {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.Arity = arity;
    }

    public string/*!*/ FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);

        return "MapSelect";
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (!(obj is MapSelect))
        return false;

      MapSelect other = (MapSelect)obj;
      return this.Arity == other.Arity;
    }

    [Pure]
    public override int GetHashCode() {
      return Arity.GetHashCode() * 2823;
    }

    public void Emit(IList<Expr>/*!*/ args, TokenTextWriter/*!*/ stream,
                     int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(args != null);
      //Contract.Requires(stream != null);
      Contract.Assume(args.Count == Arity + 1);
      Emit(args, stream, contextBindingStrength, fragileContext, false);
    }

    public static void Emit(IList<Expr>/*!*/ args, TokenTextWriter/*!*/ stream,
                            int contextBindingStrength, bool fragileContext,
                            bool withRhs) {
      Contract.Requires(args != null);
      Contract.Requires(stream != null);
      const int opBindingStrength = 0x90;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
        (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded) {
        stream.Write("(");
      }
      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      stream.Write("[");

      string sep = "";
      int lastIndex = withRhs ? args.Count - 1 : args.Count;
      for (int i = 1; i < lastIndex; ++i) {
        stream.Write(sep);
        sep = ", ";
        cce.NonNull(args[i]).Emit(stream);
      }

      if (withRhs) {
        stream.Write(" := ");
        cce.NonNull(args.Last()).Emit(stream);
      }

      stream.Write("]");
      if (parensNeeded) {
        stream.Write(")");
      }
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      // PR: nothing?
    }

    public int ArgumentCount {
      get {
        return Arity + 1;
      }
    }

    // it is assumed that each of the arguments has already been typechecked
    public static Type Typecheck(Type/*!*/ mapType,
      // we just pass an Absy, because in
      // the AssignCmd maps can also be
      // represented by non-expressions
                                 Absy/*!*/ map,
                                 List<Expr>/*!*/ indexes,
      // the type parameters, in this context, are the parameters of the
      // potentially polymorphic map type. Because it might happen that
      // the whole map type is unknown and represented using a MapTypeProxy,
      // the instantiations given in the following out-parameter are subject
      // to change if further unifications are done.
                                 out TypeParamInstantiation/*!*/ tpInstantiation,
                                 TypecheckingContext/*!*/ tc,
                                 IToken/*!*/ typeCheckingSubject,
                                 string/*!*/ opName) {
      Contract.Requires(mapType != null);
      Contract.Requires(map != null);
      Contract.Requires(indexes != null);
      Contract.Requires(tc != null);
      Contract.Requires(typeCheckingSubject != null);
      Contract.Requires(opName != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      
      mapType = mapType.Expanded;
      if (mapType.IsMap && mapType.MapArity != indexes.Count) {
        tc.Error(typeCheckingSubject, "wrong number of arguments in {0}: {1} instead of {2}",
                 opName, indexes.Count, mapType.MapArity);
        tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
        return null;
      } else if (!mapType.Unify(new MapTypeProxy(map.tok, "select", indexes.Count))) {
        tc.Error(map.tok, "{0} applied to a non-map: {1}", opName, map);
        tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
        return null;
      }
      mapType = TypeProxy.FollowProxy(mapType);

      if (mapType is MapType) {
        MapType mt = (MapType)mapType;
        return mt.CheckArgumentTypes(indexes, out tpInstantiation,
                                     typeCheckingSubject, opName, tc);
      } else {
        MapTypeProxy mt = (MapTypeProxy)mapType;
        return mt.CheckArgumentTypes(indexes, out tpInstantiation,
                                     typeCheckingSubject, opName, tc);
      }
    }

    public Type Typecheck(ref List<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Assume(args.Count == Arity + 1);

      List<Expr> actualArgs = new List<Expr>();
      for (int i = 1; i < args.Count; ++i)
        actualArgs.Add(args[i]);

      return Typecheck(cce.NonNull(cce.NonNull(args[0]).Type), cce.NonNull(args[0]),
                       actualArgs, out tpInstantiation, tc, this.tok, "map select");
    }

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Expr a0 = cce.NonNull(args[0]);
      Type a0Type = a0.ShallowType;
      if (a0Type == null || !a0Type.IsMap) {
        // we are unable to determine the type of the select, so just return an arbitrary type
        return Type.Int;
      }
      MapType mapType = a0Type.AsMap;
      List<Type> actualArgTypes = new List<Type>();
      for (int i = 1; i < args.Count; ++i) {
        actualArgTypes.Add(cce.NonNull(args[i]).ShallowType);
      }
      return Type.InferValueType(mapType.TypeParameters, mapType.Arguments, mapType.Result, actualArgTypes);
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class MapStore : IAppliable {

    public readonly int Arity;
    public readonly IToken/*!*/ tok;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }


    public MapStore(IToken tok, int arity) {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.Arity = arity;
    }

    public string/*!*/ FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);

        return "MapStore";
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (!(obj is MapStore))
        return false;

      MapStore other = (MapStore)obj;
      return this.Arity == other.Arity;
    }

    [Pure]
    public override int GetHashCode() {
      return Arity.GetHashCode() * 28231;
    }

    public void Emit(IList<Expr>/*!*/ args, TokenTextWriter/*!*/ stream,
                     int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(args != null);
      //Contract.Requires(stream != null);
      Contract.Assert(args.Count == Arity + 2);
      MapSelect.Emit(args, stream, contextBindingStrength, fragileContext, true);
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      // PR: nothing?
    }

    public int ArgumentCount {
      get {
        return Arity + 2;
      }
    }

    // it is assumed that each of the arguments has already been typechecked
    public static Type Typecheck(IList<Expr>/*!*/ args, out TypeParamInstantiation/*!*/ tpInstantiation,
                                 TypecheckingContext/*!*/ tc,
                                 IToken/*!*/ typeCheckingSubject,
                                 string/*!*/ opName) {
      Contract.Requires(args != null);
      Contract.Requires(tc != null);
      Contract.Requires(typeCheckingSubject != null);
      Contract.Requires(opName != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);

      // part of the type checking works exactly as for MapSelect
      List<Expr> selectArgs = new List<Expr>();
      for (int i = 1; i < args.Count - 1; ++i)
        selectArgs.Add(args[i]);
      Type resultType =
        MapSelect.Typecheck(cce.NonNull(cce.NonNull(args[0]).Type), cce.NonNull(args[0]),
                            selectArgs, out tpInstantiation, tc, typeCheckingSubject, opName);

      // check the the rhs has the right type
      if (resultType == null) {
        // error messages have already been created by MapSelect.Typecheck
        return null;
      }
      Type rhsType = cce.NonNull(cce.NonNull(args.Last()).Type);
      if (!resultType.Unify(rhsType)) {
        tc.Error(cce.NonNull(args.Last()).tok,
                 "right-hand side in {0} with wrong type: {1} (expected: {2})",
                 opName, rhsType, resultType);
        return null;
      }

      return cce.NonNull(args[0]).Type;
    }

    public Type Typecheck(ref List<Expr>/*!*/ args,
                          out TypeParamInstantiation/*!*/ tpInstantiation,
                          TypecheckingContext/*!*/ tc) {
      //Contract.Requires(args != null);
      //Contract.Requires(tc != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(Contract.ValueAtReturn(out args) != null);
      Contract.Assert(args.Count == Arity + 2);
      return Typecheck(args, out tpInstantiation, tc, this.tok, "map store");
    }

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return cce.NonNull(args[0]).ShallowType;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }


  public class IfThenElse : IAppliable {

    private IToken/*!*/ _tok;

    public IToken/*!*/ tok
    {
      get
      {
        Contract.Ensures(Contract.Result<IToken>() != null);
        return this._tok;
      }
      set
      {
        Contract.Requires(value != null);
        this._tok = value;
      }
    }
    
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(this._tok != null);
    }

    public IfThenElse(IToken tok) {
      Contract.Requires(tok != null);
      this._tok = tok;
    }

    public string/*!*/ FunctionName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);

        return "if-then-else";
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (!(obj is IfThenElse))
        return false;
      return true;
    }

    [Pure]
    public override int GetHashCode() {
      return 1;
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.SetToken(this);
      Contract.Assert(args.Count == 3);
      stream.push();
      stream.Write("(if ");     
      cce.NonNull(args[0]).Emit(stream, 0x00, false);
      stream.sep();
      stream.Write(" then ");
      cce.NonNull(args[1]).Emit(stream, 0x00, false);
      stream.sep();
      stream.Write(" else ");
      cce.NonNull(args[2]).Emit(stream, 0x00, false);
      stream.Write(")");
      stream.pop();
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting) {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      // PR: nothing?
    }

    public int ArgumentCount {
      get {
        return 3;
      }
    }

    public Type Typecheck(ref List<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Assert(args.Count == 3);
      // the default; the only binary operator with a type parameter is equality, but right
      // we don't store this parameter because it does not appear necessary
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      Expr arg0 = cce.NonNull(args[0]);
      Expr arg1 = cce.NonNull(args[1]);
      Expr arg2 = cce.NonNull(args[2]);

      if (!cce.NonNull(arg0.Type).Unify(Type.Bool)) {
        tc.Error(this.tok, "the first argument to if-then-else should be bool, not {0}", arg0.Type);
      } else if (!cce.NonNull(arg1.Type).Unify(cce.NonNull(arg2.Type))) {
        tc.Error(this.tok, "branches of if-then-else have incompatible types {0} and {1}", arg1.Type, arg2.Type);
      } else {
        return arg1.Type;
      }

      return null;
    }

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    public Type ShallowType(IList<Expr> args) {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return cce.NonNull(args[1]).ShallowType;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }



  public class CodeExpr : Expr {
    public List<Variable>/*!*/ LocVars;
    [Rep]
    public List<Block/*!*/>/*!*/ Blocks;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(LocVars != null);
      Contract.Invariant(cce.NonNullElements(Blocks));
    }

    public CodeExpr(List<Variable>/*!*/ localVariables, List<Block/*!*/>/*!*/ blocks, bool immutable=false)
      : base(Token.NoToken, immutable) {
      Contract.Requires(localVariables != null);
      Contract.Requires(cce.NonNullElements(blocks));
      Contract.Requires(0 < blocks.Count);
      LocVars = localVariables;
      Blocks = blocks;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    // FIXME: This seems wrong we don't want reference equality, we want structural equality
    [Pure]
    public override bool Equals(object obj)
    {
      return base.Equals(obj);
    }

    [Pure]
    public override int GetHashCode()
    {
      if (Immutable)
        return CachedHashCode;
      else
        return ComputeHashCode();
    }

    [Pure]
    public override int ComputeHashCode() {
      return base.GetHashCode();
    }


    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      // Treat a BlockEexpr as if it has no free variables at all
    }
    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      //level++;
      int level = 0;
      stream.WriteLine(level, "|{");

      if (this.LocVars.Count > 0) {
        stream.Write(level + 1, "var ");
        this.LocVars.Emit(stream, true);
        stream.WriteLine(";");
      }

      foreach (Block/*!*/ b in this.Blocks) {
        Contract.Assert(b != null);
        b.Emit(stream, level + 1);
      }

      stream.WriteLine();
      stream.WriteLine(level, "}|");

      stream.WriteLine();
      stream.WriteLine();
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);

      rc.PushVarContext();
      foreach (Variable/*!*/ v in LocVars) {
        Contract.Assert(v != null);
        v.Register(rc);
        v.Resolve(rc);
      }

      rc.PushProcedureContext();
      foreach (Block/*!*/ b in Blocks) {
        Contract.Assert(b != null);
        b.Register(rc);
      }

      foreach (Block/*!*/ b in Blocks) {
        Contract.Assert(b != null);
        b.Resolve(rc);
      }

      rc.PopProcedureContext();
      rc.PopVarContext();
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      foreach (Variable/*!*/ v in LocVars) {
        Contract.Assert(v != null);
        v.Typecheck(tc);
      }
      foreach (Block/*!*/ b in Blocks) {
        Contract.Assert(b != null);
        b.Typecheck(tc);
      }
      this.Type = Type.Bool;
    }
    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Type.Bool;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitCodeExpr(this);
    }
  }

  public class BvExtractExpr : Expr {
    // FIXME: Protect these fields
    public /*readonly--except in StandardVisitor*/ Expr/*!*/ Bitvector;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Bitvector != null);
    }

    public readonly int Start, End;

    public BvExtractExpr(IToken/*!*/ tok, Expr/*!*/ bv, int end, int start, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(bv != null);
      Bitvector = bv;
      Start = start;
      End = end;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is BvExtractExpr))
        return false;

      BvExtractExpr other = (BvExtractExpr)obj;
      return object.Equals(this.Bitvector, other.Bitvector) &&
        this.Start.Equals(other.Start) && this.End.Equals(other.End);
    }

    [Pure]
    public override int GetHashCode() {
      if (Immutable)
        return CachedHashCode;
      else
        return ComputeHashCode();
    }
    
    [Pure]
    public override int ComputeHashCode() {
      int h = this.Bitvector.GetHashCode();
      h ^= Start * 17 ^ End * 13;
      return h;
    }
    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      int opBindingStrength = 0x90;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
        (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded) {
        stream.Write("(");
      }
      Bitvector.Emit(stream, opBindingStrength, false);
      stream.Write("[" + End + ":" + Start + "]");
      if (parensNeeded) {
        stream.Write(")");
      }
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      Bitvector.Resolve(rc);
    }
    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      Bitvector.ComputeFreeVariables(freeVars);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      Bitvector.Typecheck(tc);
      Contract.Assert(Bitvector.Type != null);  // follows from postcondition of Expr.Typecheck

      if (Start < 0) {
        tc.Error(this, "start index in extract must not be negative");
      } else if (End < 0) {
        tc.Error(this, "end index in extract must not be negative");
      } else if (End < Start) {
        tc.Error(this, "start index in extract must be no bigger than the end index");
      } else {
        Type typeConstraint = new BvTypeProxy(this.tok, "extract", End - Start);
        if (typeConstraint.Unify(Bitvector.Type)) {
          Type = Type.GetBvType(End - Start);
        } else {
          tc.Error(this, "extract operand must be a bitvector of at least {0} bits (got {1})", End - Start, Bitvector.Type);
        }
      }
      if (Type == null) {
        Type = new TypeProxy(this.tok, "type_checking_error");
      }
    }

    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Type.GetBvType(End - Start);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBvExtractExpr(this);
    }
  }

  public class BvConcatExpr : Expr {
    // FIXME: Protect these fields
    public /*readonly--except in StandardVisitor*/ Expr/*!*/ E0, E1;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E0 != null);
      Contract.Invariant(E1 != null);
    }


    public BvConcatExpr(IToken/*!*/ tok, Expr/*!*/ e0, Expr/*!*/ e1, bool immutable=false)
      : base(tok, immutable) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      E0 = e0;
      E1 = e1;
      if (immutable)
        CachedHashCode = ComputeHashCode();
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is BvConcatExpr))
        return false;

      BvConcatExpr other = (BvConcatExpr)obj;
      return object.Equals(this.E0, other.E0) && object.Equals(this.E1, other.E1);
    }

    [Pure]
    public override int GetHashCode()
    {
      if (Immutable)
        return CachedHashCode;
      else
        return ComputeHashCode();
    }

    [Pure]
    public override int ComputeHashCode() {
      int h = this.E0.GetHashCode() ^ this.E1.GetHashCode() * 17;
      return h;
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      int opBindingStrength = 0x32;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
        (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded) {
        stream.Write("(");
      }
      E0.Emit(stream, opBindingStrength, false);
      stream.Write(" ++ ");
      // while this operator is associative, our incomplete axioms in int translation don't
      // make much use of it, so better stick to the actual tree shape
      E1.Emit(stream, opBindingStrength, true);
      if (parensNeeded) {
        stream.Write(")");
      }
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      E0.Resolve(rc);
      E1.Resolve(rc);
    }
    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      E0.ComputeFreeVariables(freeVars);
      E1.ComputeFreeVariables(freeVars);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      E0.Typecheck(tc);
      Contract.Assert(E0.Type != null);  // follows from postcondition of Expr.Typecheck
      E1.Typecheck(tc);
      Contract.Assert(E1.Type != null);  // follows from postcondition of Expr.Typecheck

      if (E0.Type.Unify(new BvTypeProxy(this.tok, "concat0", 0)) && E1.Type.Unify(new BvTypeProxy(this.tok, "concat1", 0))) {
        Type = new BvTypeProxy(this.tok, "concat", E0.Type, E1.Type);
      } else {
        tc.Error(this, "++ operands need to be bitvectors (got {0}, {1})", E0.Type, E1.Type);
      }
      if (Type == null) {
        Type = new TypeProxy(this.tok, "type_checking_error");
      }
    }

    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        Type t0 = E0.ShallowType;
        Type t1 = E1.ShallowType;
        int len0 = t0.IsBv ? t0.BvBits : /*expression is not type correct, so just pick an arbitrary number of bits*/0;
        int len1 = t1.IsBv ? t1.BvBits : /*expression is not type correct, so just pick an arbitrary number of bits*/0;
        return Type.GetBvType(len0 + len1);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBvConcatExpr(this);
    }
  }
}

