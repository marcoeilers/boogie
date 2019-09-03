using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Core
{
  class Translator
  {
    public static Program Translate(Program p)
    {
      // print, what p is
      Console.WriteLine();
      Console.WriteLine("Printing Program...");
      Console.WriteLine("  " + p);
      Console.WriteLine();
      
      // list all procedure and implementation names to be verified
      Console.WriteLine("Printing Procedure and Implementation Names...");
      foreach (Declaration d in p.TopLevelDeclarations)
      {
        if (d is Procedure)
          Console.WriteLine("  Procedure: " + ((Procedure)d).Name);
        else if (d is Implementation)
          Console.WriteLine("  Implementation: " + ((Implementation)d).Name);
        else
          Console.WriteLine("  Something else in TopLevelDeclarations:" + d);
      }
      Console.WriteLine();

      // here we transform the whole program
      Console.WriteLine("Transforming Program...");

      Program p_transformed = new Program();

      // read out the names of global existensial constants
      // to identify the non-user / user given invariants in implementation
      HashSet<string> existentials = new HashSet<string>();
      foreach (Declaration d in p.TopLevelDeclarations)
      {
        if (d is Constant && ((Constant)d).Attributes != null && ((Constant)d).Attributes.Key == "existential")
        {
          Constant exist = (Constant)d;
          existentials.Add(exist.Name);
        }
      }

      // add transformed TopLevelDeclarations to program (p_transformed)
      foreach (Declaration d in p.TopLevelDeclarations)
      {
        if (d is Procedure)
        {
          Procedure proc = (Procedure)d;
          Console.WriteLine("  Procedure: " + proc.Name + ". Nothing to transform");
          // TODO: maybe create new Procedure
          p_transformed.AddTopLevelDeclaration(proc);
        }
        else if (d is Implementation)
        {
          Implementation imp = (Implementation)d;
          Console.WriteLine("  Implementation: " + imp.Name);

          Console.WriteLine("    Transforming Implementation...");
          Console.WriteLine();
          Implementation imp_transformed = Transform(imp, existentials);
          Console.WriteLine("    Implementation Transformed");

          p_transformed.AddTopLevelDeclaration(imp_transformed);
        }
        else
        {
          Console.WriteLine("  Something else in TopLevelDeclarations:" + d);
          p_transformed.AddTopLevelDeclaration(d);
        }
      }
      Console.WriteLine();

      // print the program text to the console
      Console.WriteLine("Printing the Program Text...");
      PrintBplFile("-", p, true, true, true);

      // print the transformed program text to the console
      Console.WriteLine("Printing the Transformed Program Text...");
      PrintBplFile("-", p_transformed, true, true, true);

      // empty program
      Program p_other = new Program();
      Console.WriteLine("Printing the Empty Program Text...");
      PrintBplFile("-", p_other, true, true, true);

      //return p_other;
      return p_transformed;

    }
    // end Translate

    private static Implementation Transform(Implementation imp, HashSet<string> existentials)
    {
      // get all target variables names
      // get all target variables names per loop
      HashSet<string> names_of_targets = new HashSet<string>();
      Dictionary<string, HashSet<string>> names_of_targets_by_loop = new Dictionary<string, HashSet<string>>();
      foreach (BigBlock bb in imp.StructuredStmts.BigBlocks)
      {
        names_of_targets.UnionWith(GetTargetNames(bb, false));

        HashSet<string> loop_labels = new HashSet<string>();
        Dictionary<string, HashSet<string>> targets_by_loop = Collect_Target_Names_by_Loop(bb, loop_labels, false);
        names_of_targets_by_loop = MergeDictionaries(names_of_targets_by_loop, targets_by_loop);
      }

      // get invariants and user defined invariants
      // get mapping from loop_label to user's invariants
      List<PredicateCmd> invariants;
      Dictionary<string, List<Expr>> loop_2_user_invs;
      invariants = Get_Invariants(imp, existentials, out loop_2_user_invs);

      // Just for debugging
      // print all invariants and user defined invariants
      Console.WriteLine("      Printing Invariants...");
      foreach (PredicateCmd p in invariants)
      {
        Console.WriteLine("        " + p.ToString());
      }
      Console.WriteLine();

      Console.WriteLine("      Printing User Defined Invariants...");
      foreach (KeyValuePair<string, List<Expr>> kv in loop_2_user_invs)
      {
        Console.WriteLine("        Loop: " + kv.Key);
        foreach (Expr e in kv.Value) {
          Console.WriteLine("            Invariant Expression: " + e.ToString());
        }
      }
      Console.WriteLine();

      // Just for debugging
      // print target variables
      Console.WriteLine("      Printing Target Variables Names...");
      foreach (string s in names_of_targets)
      {
        Console.WriteLine("        " + s);
      }
      Console.WriteLine();

      // print target variables names according to the corresponding loop label
      Console.WriteLine("      Printing Target Variables Names by Loop Label...");
      foreach (KeyValuePair<string, HashSet<string>> key_value in names_of_targets_by_loop)
      {
        Console.WriteLine("          Label: " + key_value.Key);
        foreach (string s in key_value.Value)
        {
          Console.WriteLine("              " + s);
        }
      }
      Console.WriteLine();

      // begin of the transformation 
      // here we already have the list of target variables in names_of_targets HashSet

      // fake invariant (res <= m * i + j), just to see how it works

      // m 
      IToken tok_rhs_1_fake_inv = new Token();
      Expr rhs_1_fake_inv = new IdentifierExpr(tok_rhs_1_fake_inv, "m");
      // i 
      IToken tok_rhs_2_fake_inv = new Token();
      Expr rhs_2_fake_inv = new IdentifierExpr(tok_rhs_2_fake_inv, "i");
      // m * i
      IList<Expr> args_rhs_1_fake_inv = new List<Expr>();
      args_rhs_1_fake_inv.Add(rhs_1_fake_inv);
      args_rhs_1_fake_inv.Add(rhs_2_fake_inv);
      IToken tok_rhs_1_binary_op = new Token();
      IAppliable fun_expr_rhs_1_fake_inv = new BinaryOperator(tok_rhs_1_binary_op, BinaryOperator.Opcode.Mul);
      IToken tok_rhs_11_fake_inv = new Token();
      Expr rhs_11_fake_inv = new NAryExpr(tok_rhs_11_fake_inv, fun_expr_rhs_1_fake_inv, args_rhs_1_fake_inv);

      // j
      IToken tok_rhs_22_fake_inv = new Token();
      Expr rhs_22_fake_inv = new IdentifierExpr(tok_rhs_22_fake_inv, "j");

      // m * i + j
      IList<Expr> args_rhs_fake_inv = new List<Expr>();
      args_rhs_fake_inv.Add(rhs_11_fake_inv);
      args_rhs_fake_inv.Add(rhs_22_fake_inv);
      IToken tok_rhs_binary_op = new Token();
      IAppliable fun_expr_rhs_fake_inv = new BinaryOperator(tok_rhs_binary_op, BinaryOperator.Opcode.Add);
      IToken tok_rhs_fake_inv = new Token();
      Expr rhs_fake_inv = new NAryExpr(tok_rhs_fake_inv, fun_expr_rhs_fake_inv, args_rhs_fake_inv);

      // res
      IToken tok_lhs_fake_inv = new Token();
      Expr lhs_fake_inv = new IdentifierExpr(tok_lhs_fake_inv, "res");

      // res <= m * i + j
      IList<Expr> args_fake_inv = new List<Expr>();
      args_fake_inv.Add(lhs_fake_inv);
      args_fake_inv.Add(rhs_fake_inv);
      IToken tok_binary_op = new Token();
      IAppliable fun_expr_fake_inv = new BinaryOperator(tok_binary_op, BinaryOperator.Opcode.Le);
      IToken tok_expr_fake_inv = new Token();
      Expr expr_fake_inv = new NAryExpr(tok_expr_fake_inv, fun_expr_fake_inv, args_fake_inv);

      // assert res <= m * i + j
      IToken tok_fake_inv = new Token();
      PredicateCmd fake_inv = new AssertCmd(tok_fake_inv, expr_fake_inv);

      // end of invariant construnction
      // invariant (assert res <= m * i + j)
      // stored in fake_inv variable

      // List of candidate invariants
      IList <PredicateCmd> invariants_fake = new List<PredicateCmd>();
      invariants_fake.Add(fake_inv);

      Implementation imp_copy = (Implementation)imp.Clone(); 

      // arguments for Implementation constructor
      
      // The first 5 can be constructed directly from imp_copy parameters

      IToken tok_transformed = new Token();          
      string Name_transformed = imp_copy.Name; 

      List<Variable> InParams_transformed = new List<Variable>();
      InParams_transformed.AddRange(imp.InParams); 

      List<Variable> OutParams_transformed = new List<Variable>();
      OutParams_transformed.AddRange(imp.OutParams);

      List<TypeVariable> TypeParameters_transformed = new List<TypeVariable>();
      TypeParameters_transformed.AddRange(imp.TypeParameters);

      // The last two List parameters to have to be  constructed iteratively element by element

      // LocVars
      List<Variable> LocVars_transformed = new List<Variable>();
      LocVars_transformed.AddRange(imp_copy.LocVars);

      // here we have to add copies of target variables and boolean variables for candidate invariants
      Dictionary<string, string> targets_2_duplicates = new Dictionary<string, string>();
      HashSet<Variable> duplicates = Get_Target_Variables_Duplicates(imp_copy.LocVars, imp_copy.OutParams, names_of_targets, out targets_2_duplicates);
      LocVars_transformed.AddRange(duplicates);

      // add boolean variables on_id, on_b_id, on_a_id for each candidate invariant
      // and each loop id to LocVars
      foreach (KeyValuePair<string, HashSet<string>> key_value in names_of_targets_by_loop) {
        int inv_id = 1;
        string label = key_value.Key;
        foreach (PredicateCmd inv in invariants) {
          // on_id
          LocalVariable var_on = Create_Local_Variable(label, "_on_", inv_id, true);
          LocVars_transformed.Add(var_on);

          // on_b_id
          LocalVariable var_on_b = Create_Local_Variable(label, "_on_b_", inv_id, true);
          LocVars_transformed.Add(var_on_b);

          // on_a_id
          LocalVariable var_on_a = Create_Local_Variable(label, "_on_a_", inv_id, true);
          LocVars_transformed.Add(var_on_a);

          inv_id++;
        }

        // star_id, for actual loop ancoding
        // format: label_star
        LocalVariable star = Create_Local_Variable(label, "_star", inv_id, false);
        LocVars_transformed.Add(star);

        // lc_id to check inner loop condition
        LocalVariable lc = Create_Local_Variable(label, "_lc", inv_id, false);
        LocVars_transformed.Add(lc);
      }

      // for debugging
      Console.WriteLine("      Targets-2-Duplicates: ");
      foreach (KeyValuePair<string, string> key_value in targets_2_duplicates) {
        Console.WriteLine("          " + key_value.Key + "    " + key_value.Value);
      }
      Console.WriteLine();

      // StructuredStmts
      
      // to construct the last argument to Implementation constructor (StructuredStmts)
      // we need to construct and fill in BigBlocks List
      IList<BigBlock> BigBlocks_transformed = new List<BigBlock>();
      foreach (BigBlock b in imp_copy.StructuredStmts.BigBlocks) {
        IList<BigBlock> b_transformed = Transform_BigBlock_not_in_loop(b, invariants, names_of_targets_by_loop, targets_2_duplicates);
        foreach (BigBlock bb in b_transformed) {
          BigBlocks_transformed.Add(bb);
        }
      }
      
      // second argument for StructuredStmts constructor
      IToken EndCurly_transformed = new Token
      {
        val = "}"
      };

      StmtList StructuredStmts_transformed = new StmtList(BigBlocks_transformed, EndCurly_transformed);
     
      Implementation imp_transformed = new Implementation(tok_transformed, Name_transformed,
        TypeParameters_transformed, InParams_transformed, OutParams_transformed, 
        LocVars_transformed, StructuredStmts_transformed);

      return imp_transformed;
    }
    // end Transform

    // the method goes through the whole implementation 
    // and reads off all the invariants
    // the output is the list of candidate invariants
    // and the dictionary of user defined invariants per loop
    // already_seen_existentials parameter is needed in order not to insert
    // the same invariant twice in the res
    private static List<PredicateCmd> Get_Invariants(Implementation imp, HashSet<string> existentials, out Dictionary<string, List<Expr>> loop_2_user_invs)
    {
      List<PredicateCmd> res = new List<PredicateCmd>();
      loop_2_user_invs = new Dictionary<string, List<Expr>>();

      HashSet<string> already_seen_existentials = new HashSet<string>();

      HashSet<string> already_seen_existentials_out;
      Dictionary<string, List <Expr>> loop_2_user_invs_out;

      foreach (BigBlock bb in imp.StructuredStmts.BigBlocks) {
        res.AddRange(Get_Invariants_From_BigBlock(bb, existentials, already_seen_existentials, out already_seen_existentials_out, out loop_2_user_invs_out));
        foreach (string e_name in already_seen_existentials_out) {
          already_seen_existentials.Add(e_name);
        }
        foreach (KeyValuePair<string, List<Expr>> kv in loop_2_user_invs_out) {
          if (!loop_2_user_invs.ContainsKey(kv.Key)) {
            // since we do not visit the same BigBlock twice, if condition should always be satisfied
            loop_2_user_invs.Add(kv.Key, kv.Value);
          }
        }
      }

      return res;
    }
    // end Get_Invariants

    // the method goes through a single BigBlock 
    // and reads off all the invariants
    // the output is the list of candidate invariants
    // and the dictionary of user defined invariants per loop
    // from this single BigBlock
    // already_seen_existentials parameter is needed in order not to insert
    // the same invariant twice in the res
    private static List<PredicateCmd> Get_Invariants_From_BigBlock(BigBlock bb, HashSet<string> existentials, HashSet<string> already_seen_existentials, out HashSet<string> already_seen_existentials_out, out Dictionary<string, List<Expr>> loop_2_user_invs)
    {
      List<PredicateCmd> res = new List<PredicateCmd>();
      loop_2_user_invs = new Dictionary<string, List<Expr>>();

      already_seen_existentials_out = new HashSet<string>();
      Dictionary<string, List<Expr>> loop_2_user_invs_out;

      // no implementation for BreakCmd for now

      if (bb.ec is WhileCmd)
      {
        WhileCmd w = (WhileCmd)bb.ec;

        // read the invariants of this loop off
        // the assumption is that each user defined invariant appears at most once per loop
        List<Expr> user_invs = new List<Expr>();
        List<PredicateCmd> invs = w.Invariants;
        foreach (PredicateCmd inv in invs)
        {
          Expr e = inv.Expr;
          if (e is NAryExpr &&
            (((NAryExpr)e).Args[0] is IdentifierExpr && existentials.Contains(((IdentifierExpr)((NAryExpr)e).Args[0]).Name)))
          { // non-user invariant
            string e_name = ((IdentifierExpr)((NAryExpr)e).Args[0]).Name;
            if (!already_seen_existentials.Contains(e_name))
            { // we add an invariant to the output list only if we haven't seen it before
              already_seen_existentials_out.Add(e_name);

              Expr inv_expr = ((NAryExpr)e).Args[1];
              IToken tok_inv = new Token();
              // it is not necessary to wrap inv_expr in a PredicateCmd
              // but other methods expect an instance of a PredicateCmd
              PredicateCmd invariant = new AssertCmd(tok_inv, inv_expr);
              res.Add(invariant);
            }
          }
          else
          { // user's invariant
            user_invs.Add(e);
          }
        }

        if (user_invs.Count > 0 && !loop_2_user_invs.ContainsKey(bb.LabelName))
        { // should always be the case, since we do not visit the same BigBlock twice
          loop_2_user_invs.Add(bb.LabelName, user_invs);
        }

        // get invariants from BigBlocks of while
        HashSet<string> all_seen_invs = new HashSet<string>();
        foreach (string s in already_seen_existentials) {
          all_seen_invs.Add(s);
        }
        foreach (string s in already_seen_existentials_out)
        {
          all_seen_invs.Add(s);
        }

        HashSet<string> all_seen_invs_out;
        foreach (BigBlock b in w.Body.BigBlocks) {
          res.AddRange(Get_Invariants_From_BigBlock(b, existentials, all_seen_invs, out all_seen_invs_out, out loop_2_user_invs_out));
          foreach (string s in all_seen_invs_out) {
            all_seen_invs.Add(s);
            already_seen_existentials_out.Add(s);
          }

          foreach (KeyValuePair<string, List<Expr>> kv in loop_2_user_invs_out) {
            if (!loop_2_user_invs.ContainsKey(kv.Key))
            { // since we do not visit the same BigBlock twice, if condition should always be satisfied
              loop_2_user_invs.Add(kv.Key, kv.Value);
            }
          }
        }
      }
      else if (bb.ec is IfCmd)
      {
        IfCmd ec_if = (IfCmd)bb.ec;
        res.AddRange(Get_Invariants_From_If(ec_if, existentials, already_seen_existentials, out already_seen_existentials_out, out loop_2_user_invs));
      }     

      return res;
    }
    // end Get_Invariants_From_Big_Block

    // the method returns all not already collected invariants from an if statement
    // user invariants per loop are returned in loop_2_user_invs parameter 
    private static List<PredicateCmd> Get_Invariants_From_If(IfCmd ec_if, HashSet<string> existentials, HashSet<string> already_seen_existentials, out HashSet<string> already_seen_existentials_out ,out Dictionary<string, List<Expr>> loop_2_user_invs)
    {
      List<PredicateCmd> res = new List<PredicateCmd>();
      loop_2_user_invs = new Dictionary<string, List<Expr>>();
      already_seen_existentials_out = new HashSet<string>();

      Dictionary<string, List<Expr>> loop_2_user_invs_out;
      HashSet<string> all_seen_existentials = new HashSet<string>();
      HashSet<string> all_seen_existentials_out;

      foreach (string s in already_seen_existentials) {
        all_seen_existentials.Add(s);
      }

      // then
      if (ec_if.thn != null)
      {
        foreach (BigBlock bb in ec_if.thn.BigBlocks) {
          res.AddRange(Get_Invariants_From_BigBlock(bb, existentials, all_seen_existentials, out all_seen_existentials_out, out loop_2_user_invs_out));
          foreach (string s in all_seen_existentials_out) {
            all_seen_existentials.Add(s);
            already_seen_existentials_out.Add(s);
          }

          foreach (KeyValuePair<string, List<Expr>> kv in loop_2_user_invs_out) {
            if (!loop_2_user_invs.ContainsKey(kv.Key))
            { // since we do not visit the same BigBlock twice, if condition should always be satisfied
              loop_2_user_invs.Add(kv.Key, kv.Value);
            }
          }
        }
      }

      // else if
      if (ec_if.elseIf != null)
      {
        res.AddRange(Get_Invariants_From_If(ec_if.elseIf, existentials, all_seen_existentials, out all_seen_existentials_out, out loop_2_user_invs_out));
        foreach (string s in all_seen_existentials_out)
        {
          all_seen_existentials.Add(s);
          already_seen_existentials_out.Add(s);
        }

        foreach (KeyValuePair<string, List<Expr>> kv in loop_2_user_invs_out)
        {
          if (!loop_2_user_invs.ContainsKey(kv.Key))
          { // since we do not visit the same BigBlock twice, if condition should always be satisfied
            loop_2_user_invs.Add(kv.Key, kv.Value);
          }
        }
      }

      // else
      if (ec_if.elseBlock != null)
      {
        foreach (BigBlock bb in ec_if.elseBlock.BigBlocks)
        {
          res.AddRange(Get_Invariants_From_BigBlock(bb, existentials, all_seen_existentials, out all_seen_existentials_out, out loop_2_user_invs_out));
          foreach (string s in all_seen_existentials_out)
          {
            all_seen_existentials.Add(s);
            already_seen_existentials_out.Add(s);
          }

          foreach (KeyValuePair<string, List<Expr>> kv in loop_2_user_invs_out)
          {
            if (!loop_2_user_invs.ContainsKey(kv.Key))
            { // since we do not visit the same BigBlock twice, if condition should always be satisfied
              loop_2_user_invs.Add(kv.Key, kv.Value);
            }
          }
        }
      }

      return res;
    }
    // end Get_Invariants_From_If

    // method creates a local variable with name based on the loop_label, 
    // free extenstion and the index of an invariant in the invariants list
    // boolean parameter indicates, whether to use inv_id as part of the variable name
    // form of the name: loop_label + name_extention + inv_id 
    // or loop_label + name_extention
    // example: anon8_on_b_1
    private static LocalVariable Create_Local_Variable(string loop_label, string name_extension, int inv_id, bool all_args)
    {
      LocalVariable res;
     
      IToken tok_for_basicType = new Token();
      BasicType b_type = new BasicType(tok_for_basicType, SimpleType.Bool);

      IToken tok_for_typeIdent = new Token();

      string var_name;
      if (all_args)
      {
        var_name = loop_label + name_extension + inv_id;
      }
      else {
        var_name = loop_label + name_extension;
      }

      TypedIdent t_Ident = new TypedIdent(tok_for_typeIdent, var_name, b_type);

      IToken tok_for_var = new Token();
      res = new LocalVariable(tok_for_var, t_Ident);

      return res;
    }
    // end Create_Local_Variable

    // the method takes a BigBlock from an original Implementation and
    // a flag wether we are inside a loop
    // the original BigBlock is transformed according to the flag in_loop and corresponding encoding
    // and returned as a new object (transformation is not in place)
    private static IList<BigBlock> Transform_BigBlock_not_in_loop(BigBlock b, IList<PredicateCmd> invariants, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates)
    {
      IList<BigBlock> res = new List<BigBlock>();

      // no implementation for BreakCmd for now
      // since we are not in a loop it does not matter here
      if (b.ec is WhileCmd)
      {
        WhileCmd ec_while = (WhileCmd)b.ec;
        List<string> loops_traversed = new List<string>();
        loops_traversed.Add(b.LabelName);
        res = Transform_While(ec_while, b.simpleCmds, invariants, targets_by_loop, targets_2_duplicates, loops_traversed);
      }
      else if (b.ec is IfCmd)
      {
        IToken t_transformed = new Token();
        string label_transformed = b.LabelName + "_transformed";
        // simple commands: assignment (also with method call), assume, assert, havoc
        // are not affected outside a loop
        List<Cmd> simpleCmds_transformed = b.simpleCmds;

        // I do not know, what it is
        TransferCmd tc_transformed = b.tc;

        IfCmd ec_if = (IfCmd)b.ec;
        StructuredCmd ec_transformed;
        ec_transformed = Transform_If(ec_if, invariants, targets_by_loop, targets_2_duplicates, null, false);

        BigBlock b_transformed = new BigBlock(t_transformed, label_transformed, simpleCmds_transformed, ec_transformed, tc_transformed);
        res.Add(b_transformed);
      }
      else 
      {
        IToken t_transformed = new Token();
        string label_transformed = b.LabelName + "_transformed";
        // simple commands: assignment (also with method call), assume, assert, havoc
        // are not affected outside a loop
        List<Cmd> simpleCmds_transformed = b.simpleCmds;

        // I do not know, what it is
        TransferCmd tc_transformed = b.tc;

        StructuredCmd ec_transformed;
        ec_transformed = b.ec;

        BigBlock b_transformed = new BigBlock(t_transformed, label_transformed, simpleCmds_transformed, ec_transformed, tc_transformed);
        res.Add(b_transformed);
      }

      return res;
    }
    // end transform_BigBlock_not_in_loop

    // The method transformes BigBlock, which contains a WhileCmd;
    // Parameters ec_while and simpleCmds 
    // are the corresponding fields of the BigBlock under transformation;
    // Transformation results in multiple BigBlocks;
    // Parameter simpleCmds is added at the beginning 
    // of simpleCmds of the first one of returned BigBlocks;
    private static IList<BigBlock> Transform_While(WhileCmd ec_while, List<Cmd> simpleCmds, IList<PredicateCmd> invariants, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed)
    {
      IList<BigBlock> res = new List<BigBlock>();

      bool USE_COMPLEX_TRAFO = true;

      if (loops_traversed.Count == 1) // this is an implicit indication that we are in the outer loop
      {
        // here we construct the first BigBlock
        
        // create simple commands for the first BigBlock

        // check, whether an invariant holds before the loop
        // no variable names replacement necessary here
        // expression form: assume inv <==> loop_label_on_b
        int id = 1;
        foreach (PredicateCmd p in invariants) {
          // get invariant
          Expr inv = p.Expr;
          
          // create expression for boolean variable (right hand sight)
          IToken tok_on_b = new Token();
          string name_on_b = loops_traversed[0] + "_on_b_" + id;
          Expr on_b = new IdentifierExpr(tok_on_b, name_on_b);
          
          // create expression inv <==> on_b
          IToken tok_inv_on_b = new Token();
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Iff);
          IList<Expr> args = new List<Expr>();
          args.Add(inv);
          args.Add(on_b);
          Expr inv_on_b = new NAryExpr(tok_inv_on_b, fun, args);

          // create assumption command: assume inv <==> on_b
          IToken tok_assume = new Token();
          Cmd assumeStmt = new AssumeCmd(tok_assume, inv_on_b);

          // add assumption to the end of the simpleCmds list
          simpleCmds.Add(assumeStmt);

          id++;
        }

        // simulate an arbitrary iteration of the loop

        // havoc targets
        HashSet<string> targets;
        targets_by_loop.TryGetValue(loops_traversed[0], out targets);
        foreach (string var in targets) {
          // create IdentifierExpr for duplicate of a target variable
          string duplicate_name;
          targets_2_duplicates.TryGetValue(var, out duplicate_name);
          IToken tok_duplicate = new Token();
          IdentifierExpr duplicate_var = new IdentifierExpr(tok_duplicate, duplicate_name);
         
          // create havocCmd
          IToken tok_havoc = new Token();
          List<IdentifierExpr> vars = new List<IdentifierExpr>();
          vars.Add(duplicate_var);
          Cmd havoc_target = new HavocCmd(tok_havoc, vars);

          // add havoc statement to the end of the simpleCmds list
          simpleCmds.Add(havoc_target);
        }

        // add statements of the form 
        // assume on_a ==> inv_with_replaced_targets
        id = 1;
        foreach (PredicateCmd p in invariants)
        {
          // get invariant and replace target variables names
          Expr inv = p.Expr;
          Expr inv_replaced = Replace_Target_Names(inv, targets_by_loop, targets_2_duplicates, loops_traversed);

          // create expression for boolean variable (left hand sight)
          IToken tok_on_a = new Token();
          string name_on_a = loops_traversed[0] + "_on_a_" + id;
          Expr on_a = new IdentifierExpr(tok_on_a, name_on_a);

          // create expression on_a ==> inv_replaced
          IToken tok_inv_on_a = new Token();
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Imp);
          IList<Expr> args = new List<Expr>();
          args.Add(on_a);
          args.Add(inv_replaced);
          Expr inv_on_a = new NAryExpr(tok_inv_on_a, fun, args);

          // create assumption command: assume on_a ==> inv_replaced
          IToken tok_assume = new Token();
          Cmd assumeStmt = new AssumeCmd(tok_assume, inv_on_a);

          // add assumption to the end of the simpleCmds list
          simpleCmds.Add(assumeStmt);

          id++;
        }

        // here we are done with simpleCmds for the first BigBlock

        // we only simulate the outer loop, if we can ever enter it
        // we do not need the duplicates in the if clause for the outer loop

        // create ec field (IfCmd) for the first BigBlock
        // we only need "then" part, else_if and else are "null"

        // assume loop condition
        Expr loop_cond = Replace_Target_Names(ec_while.Guard, targets_by_loop, targets_2_duplicates, loops_traversed);
        IToken tok_assume_loop_first_bb = new Token();
        Cmd assume_loop_cond = new AssumeCmd(tok_assume_loop_first_bb, loop_cond);

        // transformed loop body
        IList<BigBlock> transformed_loop_body = new List<BigBlock>();
        foreach (BigBlock bb in ec_while.Body.BigBlocks) {
          IList<BigBlock> transformed_bb = Transform_BigBlock_simulation_loop(bb, invariants, targets_by_loop, targets_2_duplicates, loops_traversed);
          foreach (BigBlock b in transformed_bb) {
            transformed_loop_body.Add(b);
          }
        }

        // add loop condition assumtion to the beginning of the simple commands list
        // of the first BigBlock in the transformed loop body
        transformed_loop_body[0].simpleCmds.Insert(0, assume_loop_cond);

        
        IToken endCurly = new Token
        {
          val = "}"
        };
        StmtList then = new StmtList(transformed_loop_body, endCurly);
        IToken tok_if_first_bb = new Token();
        StructuredCmd ec_if_first_bb = new IfCmd(tok_if_first_bb, ec_while.Guard, then, null, null);

        // create the first BigBlock
        IToken tok_first_bb = new Token();
        string label_name_first_bb = loops_traversed[0] + "_first_bb";
        BigBlock first_bb = new BigBlock(tok_first_bb, label_name_first_bb, simpleCmds, ec_if_first_bb, null);

        // construct the second BigBlock
        // here the list of simpleCmds is empty

        // infer, which invariants hold
        IToken tok_second_bb = new Token();
        List<Cmd> simple_Cmds_second_bb = new List<Cmd>();
        string label_name_second_bb = loops_traversed[0] + "_second_bb";
        AssumeCmd assumption = Infer_Invariants_Stmt(invariants, loops_traversed[0], targets_by_loop, targets_2_duplicates, loops_traversed);
        BigBlock second_bb;
        if (!USE_COMPLEX_TRAFO)
        {
          simple_Cmds_second_bb.Add(assumption);
          second_bb = new BigBlock(tok_second_bb, label_name_second_bb, simple_Cmds_second_bb, null, null);
        }
        else
        {
          StructuredCmd ec_if_second_bb = Infer_Invariants_Stmt_Complex(invariants, loops_traversed[0], targets_by_loop, targets_2_duplicates, loops_traversed);
          second_bb = new BigBlock(tok_second_bb, label_name_second_bb, simple_Cmds_second_bb, ec_if_second_bb, null);
        }



        // construct the third BigBlock

        IToken tok_third_bb = new Token();
        string label_name_third_bb = loops_traversed[0] + "_third_bb";

        List<Cmd> simple_Cmds_third_bb = new List<Cmd>();

        // this is to be able to infer invariants for the inner loops
        for (int i = 0; i < invariants.Count; i++) {
          IToken tok_on_i = new Token();
          IToken tok_on_a_i = new Token();
          int ident = i + 1;
          string name_on_i = loops_traversed[0] + "_on_" + ident;
          string name_on_a_i = loops_traversed[0] + "_on_a_" + ident;
          Expr on_i = new IdentifierExpr(tok_on_i, name_on_i);
          Expr on_a_i = new IdentifierExpr(tok_on_a_i, name_on_a_i);

          // on_i ==> on_a_i
          IList<Expr> args = new List<Expr>();
          args.Add(on_i);
          args.Add(on_a_i);
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Imp);
          IToken tok_on_imp_on_a = new Token();
          Expr on_imp_on_a = new NAryExpr(tok_on_imp_on_a, fun, args);

          // assume on_i ==> on_a_i
          IToken tok_assume = new Token();
          Cmd new_assume = new AssumeCmd(tok_assume, on_imp_on_a);
          //MARCO:UNSOUND
          //simple_Cmds_third_bb.Add(new_assume);
        }

        // actual loop

        // star := havoc
        IToken tok_star_id = new Token();
        string name_star_id = loops_traversed[0] + "_star";
        IdentifierExpr star_id = new IdentifierExpr(tok_star_id, name_star_id);
        List<IdentifierExpr> vars_star = new List<IdentifierExpr>();
        vars_star.Add(star_id);
        IToken tok_havoc_star = new Token();
        Cmd havoc_star = new HavocCmd(tok_havoc_star, vars_star);

        simple_Cmds_third_bb.Add(havoc_star);

        // havoc targets
        foreach (string var_name in targets) {
          IToken tok_var = new Token();
          IdentifierExpr var = new IdentifierExpr(tok_star_id, var_name);
          List<IdentifierExpr> vars_targets = new List<IdentifierExpr>();
          vars_targets.Add(var);
          IToken tok_havoc_target = new Token();
          Cmd havoc_target = new HavocCmd(tok_havoc_target, vars_targets);

          simple_Cmds_third_bb.Add(havoc_target);
        }

        // assume on_i ==> inv_i
        id = 1;
        foreach (PredicateCmd p in invariants) {
          Expr inv = p.Expr;

          IToken tok_on_i = new Token();
          string name_on_i = loops_traversed[0] + "_on_" + id;
          Expr on_i = new IdentifierExpr(tok_on_i, name_on_i);
          
          // on_i ==> inv_i
          IList<Expr> args = new List<Expr>();
          args.Add(on_i);
          args.Add(inv);
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Imp);
          IToken tok_on_imp_inv = new Token();
          Expr on_imp_inv = new NAryExpr(tok_on_imp_inv, fun, args);

          // assume on_i ==> inv_i
          IToken tok_assume = new Token();
          Cmd new_assume = new AssumeCmd(tok_assume, on_imp_inv);
          simple_Cmds_third_bb.Add(new_assume);

          id++;
        }

        // if (star) then ...

        // then
        IList<BigBlock> then_bbs_third_bb = new List<BigBlock>();
        foreach (BigBlock bb in ec_while.Body.BigBlocks) {
          IList<BigBlock> bb_transformed = Transform_BigBlock_original_loop(bb, invariants, targets_by_loop, loops_traversed);
          foreach (BigBlock b in bb_transformed) {
            then_bbs_third_bb.Add(b);
          }
        }
        IToken tok_assume_guard = new Token();
        Cmd assume_guard = new AssumeCmd(tok_assume_guard, ec_while.Guard);

        then_bbs_third_bb[0].simpleCmds.Insert(0, assume_guard);

        // assume false BigBlock
        // if necessary
        IToken tok_lit = new Token();
        Expr false_lit = new LiteralExpr(tok_lit, false);
        IToken tok_assume_false = new Token();
        Cmd assume_false_cmd = new AssumeCmd(tok_assume_false, false_lit);

        int last_index = then_bbs_third_bb.Count - 1;
        if (then_bbs_third_bb[last_index].ec != null)
        {
          List<Cmd> false_lit_list = new List<Cmd>();
          false_lit_list.Add(assume_false_cmd);

          IToken tok_assume_false_bb = new Token();
          string label_assume_false_bb = loops_traversed[0] + "_assume_false_bb";
          BigBlock assume_false_bb = new BigBlock(tok_assume_false_bb, label_assume_false_bb, false_lit_list, null, null);

          then_bbs_third_bb.Add(assume_false_bb);
        }
        else
        {
          then_bbs_third_bb[last_index].simpleCmds.Add(assume_false_cmd);
        }

        IToken endCurly_then_third_bb = new Token
        {
          val = "}"
        };
        StmtList then_third_bb = new StmtList(then_bbs_third_bb, endCurly_then_third_bb);

        // else
        IList<Expr> args_not_loop_condition = new List<Expr>();
        args_not_loop_condition.Add(ec_while.Guard);
        IToken tok_fun_not_loop_condition = new Token();
        IAppliable fun_not_loop_condition = new UnaryOperator(tok_fun_not_loop_condition, UnaryOperator.Opcode.Not);
        IToken tok_not_loop_condition = new Token();
        Expr not_loop_condition = new NAryExpr(tok_not_loop_condition, fun_not_loop_condition, args_not_loop_condition);

        IToken tok_assume_not_loop_condition = new Token();
        Cmd assume_not_loop_condition = new AssumeCmd(tok_assume_not_loop_condition, not_loop_condition);
        List<Cmd> cmd_negate_loop_condition = new List<Cmd>();
        cmd_negate_loop_condition.Add(assume_not_loop_condition);

        IToken tok_negate_loop_condition = new Token();
        string name_negate_loop_condition = loops_traversed[0] + "_negate_loop_condition_bb";
        BigBlock negate_loop_condition = new BigBlock(tok_negate_loop_condition, name_negate_loop_condition, cmd_negate_loop_condition, null, null);
        IList<BigBlock> else_bbs_list = new List<BigBlock>();
        else_bbs_list.Add(negate_loop_condition);
        IToken endCurly_else_third_bb = new Token
        {
          val = "}"
        };
        StmtList else_third_bb = new StmtList(else_bbs_list, endCurly_else_third_bb);

        IToken tok_guard_third_bb = new Token();
        string name_guard_third_bb = loops_traversed[0] + "_star";
        Expr guard_ec_third_bb = new IdentifierExpr(tok_guard_third_bb, name_guard_third_bb);

        IToken tok_ec_if_third_bb = new Token();
        StructuredCmd ec_if_third_bb = new IfCmd(tok_ec_if_third_bb, guard_ec_third_bb, then_third_bb, null, else_third_bb);

        BigBlock third_bb = new BigBlock(tok_third_bb, label_name_third_bb, simple_Cmds_third_bb, ec_if_third_bb, null);

        res.Add(first_bb);
        res.Add(second_bb);
        res.Add(third_bb);
      }
      else if (loops_traversed.Count > 1) // we are in some inner loop
      {
        int last_loop_index = loops_traversed.Count - 1; // we are in this loop

        // here we construct the first BigBlock

        // create simple commands for the first BigBlock

        // check, whether an invariant holds before the loop
        // expression form: assume inv_replaced <==> loop_label_on_b
        int id = 1;
        foreach (PredicateCmd p in invariants)
        {
          // get invariant
          Expr inv = p.Expr;
          Expr inv_replaced = Replace_Target_Names(inv, targets_by_loop, targets_2_duplicates, loops_traversed);

          // create expression for boolean variable (right hand sight)
          IToken tok_on_b = new Token();
          string name_on_b = loops_traversed[last_loop_index] + "_on_b_" + id;
          Expr on_b = new IdentifierExpr(tok_on_b, name_on_b);

          // create expression inv_replaced <==> on_b
          IToken tok_inv_on_b = new Token();
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Iff);
          IList<Expr> args = new List<Expr>();
          args.Add(inv_replaced);
          args.Add(on_b);
          Expr inv_on_b = new NAryExpr(tok_inv_on_b, fun, args);

          // create assumption command: assume inv <==> on_b
          IToken tok_assume = new Token();
          Cmd assumeStmt = new AssumeCmd(tok_assume, inv_on_b);

          // add assumption to the end of the simpleCmds list
          simpleCmds.Add(assumeStmt);

          id++;
        }

        // check the inner loop condition
        Expr left = Replace_Target_Names(ec_while.Guard, targets_by_loop, targets_2_duplicates, loops_traversed);
        IToken tok_right = new Token();
        string name_right = loops_traversed[last_loop_index] + "_lc";
        Expr right = new IdentifierExpr(tok_right, name_right);

        IList<Expr> args_check_lc = new List<Expr>();
        args_check_lc.Add(left);
        args_check_lc.Add(right);
        IToken tok_fun_check_lc = new Token();
        IAppliable fun_check_lc = new BinaryOperator(tok_fun_check_lc, BinaryOperator.Opcode.Iff);
        IToken tok_check_lc = new Token();
        Expr check_lc = new NAryExpr(tok_check_lc, fun_check_lc, args_check_lc);
        IToken tok_lc = new Token();
        Cmd check_loop_condition = new AssumeCmd(tok_lc, check_lc);

        simpleCmds.Add(check_loop_condition);

        // simulate an arbitrary iteration of the loop

        // havoc targets
        HashSet<string> targets;
        targets_by_loop.TryGetValue(loops_traversed[last_loop_index], out targets);
        foreach (string var in targets)
        {
          // create IdentifierExpr for duplicate of a target variable
          string duplicate_name;
          targets_2_duplicates.TryGetValue(var, out duplicate_name);
          IToken tok_duplicate = new Token();
          IdentifierExpr duplicate_var = new IdentifierExpr(tok_duplicate, duplicate_name);

          // create havocCmd
          IToken tok_havoc = new Token();
          List<IdentifierExpr> vars = new List<IdentifierExpr>();
          vars.Add(duplicate_var);
          Cmd havoc_target = new HavocCmd(tok_havoc, vars);

          // add havoc statement to the end of the simpleCmds list
          simpleCmds.Add(havoc_target);
        }

        // add statements of the form 
        // assume on_a ==> inv_with_replaced_targets
        id = 1;
        foreach (PredicateCmd p in invariants)
        {
          // get invariant and replace target variables names
          Expr inv = p.Expr;
          Expr inv_replaced = Replace_Target_Names(inv, targets_by_loop, targets_2_duplicates, loops_traversed);

          // create expression for boolean variable (left hand sight)
          IToken tok_on_a = new Token();
          string name_on_a = loops_traversed[last_loop_index] + "_on_a_" + id;
          Expr on_a = new IdentifierExpr(tok_on_a, name_on_a);

          // create expression on_a ==> inv_replaced
          IToken tok_inv_on_a = new Token();
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Imp);
          IList<Expr> args = new List<Expr>();
          args.Add(on_a);
          args.Add(inv_replaced);
          Expr inv_on_a = new NAryExpr(tok_inv_on_a, fun, args);

          // create assumption command: assume on_a ==> inv_replaced
          IToken tok_assume = new Token();
          Cmd assumeStmt = new AssumeCmd(tok_assume, inv_on_a);

          // add assumption to the end of the simpleCmds list
          simpleCmds.Add(assumeStmt);

          id++;
        }

        // here we are done with simpleCmds for the first BigBlock

        // we only simulate the inner loop, if we can ever enter it
        
        // create ec field (IfCmd) for the first BigBlock
        // we only need "then" part, else_if and else are "null"

        // assume loop condition
        Expr loop_cond = Replace_Target_Names(ec_while.Guard, targets_by_loop, targets_2_duplicates, loops_traversed);
        IToken tok_assume_loop_first_bb = new Token();
        Cmd assume_loop_cond = new AssumeCmd(tok_assume_loop_first_bb, loop_cond);

        // transformed loop body
        IList<BigBlock> transformed_loop_body = new List<BigBlock>();
        foreach (BigBlock bb in ec_while.Body.BigBlocks)
        {
          IList<BigBlock> transformed_bb = Transform_BigBlock_simulation_loop(bb, invariants, targets_by_loop, targets_2_duplicates, loops_traversed);
          foreach (BigBlock b in transformed_bb)
          {
            transformed_loop_body.Add(b);
          }
        }

        // add loop condition assumtion to the beginning of the simple commands list
        // of the first BigBlock in the transformed loop body
        transformed_loop_body[0].simpleCmds.Insert(0, assume_loop_cond);

        IToken endCurly = new Token
        {
          val = "}"
        };
        StmtList then = new StmtList(transformed_loop_body, endCurly);

        IToken tok_lc_ident = new Token();
        string name_lc_ident = loops_traversed[last_loop_index] + "_lc";
        Expr lc_ident = new IdentifierExpr(tok_lc_ident, name_lc_ident);
        IToken tok_if_first_bb = new Token();
        StructuredCmd ec_if_first_bb = new IfCmd(tok_if_first_bb, lc_ident, then, null, null);

        // create the first BigBlock
        IToken tok_first_bb = new Token();
        string label_name_first_bb = loops_traversed[last_loop_index] + "_first_bb";
        BigBlock first_bb = new BigBlock(tok_first_bb, label_name_first_bb, simpleCmds, ec_if_first_bb, null);

        // construct the second BigBlock
        // here the list of simpleCmds is empty

        // infer, which invariants hold
        IToken tok_second_bb = new Token();
        List<Cmd> simple_Cmds_second_bb = new List<Cmd>();
        string label_name_second_bb = loops_traversed[last_loop_index] + "_second_bb";
        AssumeCmd second_assumption = Infer_Invariants_Stmt(invariants, loops_traversed[last_loop_index], targets_by_loop, targets_2_duplicates, loops_traversed);
        BigBlock second_bb;
        if (!USE_COMPLEX_TRAFO)
        {
          simple_Cmds_second_bb.Add(second_assumption);
          second_bb = new BigBlock(tok_second_bb, label_name_second_bb, simple_Cmds_second_bb, null, null);
        }
        else
        {
          StructuredCmd ec_if_second_bb = Infer_Invariants_Stmt_Complex(invariants, loops_traversed[last_loop_index], targets_by_loop, targets_2_duplicates, loops_traversed);
          second_bb = new BigBlock(tok_second_bb, label_name_second_bb, simple_Cmds_second_bb, ec_if_second_bb, null);
        }



        // construct the third BigBlock

        IToken tok_third_bb = new Token();
        string label_name_third_bb = loops_traversed[last_loop_index] + "_third_bb";

        List<Cmd> simple_Cmds_third_bb = new List<Cmd>();

        // this is to be able to infer invariants for the inner loops
        for (int i = 0; i < invariants.Count; i++)
        {
          IToken tok_on_i = new Token();
          IToken tok_on_a_i = new Token();
          int ident = i + 1;
          string name_on_i = loops_traversed[last_loop_index] + "_on_" + ident;
          string name_on_a_i = loops_traversed[last_loop_index] + "_on_a_" + ident;
          Expr on_i = new IdentifierExpr(tok_on_i, name_on_i);
          Expr on_a_i = new IdentifierExpr(tok_on_a_i, name_on_a_i);

          // on_i ==> on_a_i
          IList<Expr> args = new List<Expr>();
          args.Add(on_i);
          args.Add(on_a_i);
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Imp);
          IToken tok_on_imp_on_a = new Token();
          Expr on_imp_on_a = new NAryExpr(tok_on_imp_on_a, fun, args);

          // assume on_i ==> on_a_i
          IToken tok_assume = new Token();
          Cmd new_assume = new AssumeCmd(tok_assume, on_imp_on_a);
          // MARCO: THIS IS UNSOUND
          //simple_Cmds_third_bb.Add(new_assume);
        }

        // we are out of the loop here

        // assume !(loop_condition_replaced)
        IList<Expr> args_not_loop_condition = new List<Expr>();
        args_not_loop_condition.Add(loop_cond);
        IToken tok_fun_not_loop_condition = new Token();
        IAppliable fun_not_loop_condition = new UnaryOperator(tok_fun_not_loop_condition, UnaryOperator.Opcode.Not);
        IToken tok_not_loop_condition = new Token();
        Expr not_loop_condition = new NAryExpr(tok_not_loop_condition, fun_not_loop_condition, args_not_loop_condition);

        IToken tok_not_lc_cmd = new Token();
        Cmd not_lc_cmd = new AssumeCmd(tok_not_lc_cmd, not_loop_condition);

        simple_Cmds_third_bb.Add(not_lc_cmd);

        // assume on_i ==> inv_i_replaced
        id = 1;
        foreach (PredicateCmd p in invariants)
        {
          Expr inv = p.Expr;
          Expr inv_replaced = Replace_Target_Names(inv, targets_by_loop, targets_2_duplicates, loops_traversed);

          IToken tok_on_i = new Token();
          string name_on_i = loops_traversed[last_loop_index] + "_on_" + id;
          Expr on_i = new IdentifierExpr(tok_on_i, name_on_i);

          // on_i ==> inv_i_replaced
          IList<Expr> args = new List<Expr>();
          args.Add(on_i);
          args.Add(inv_replaced);
          IToken tok_fun = new Token();
          IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.Imp);
          IToken tok_on_imp_inv = new Token();
          Expr on_imp_inv = new NAryExpr(tok_on_imp_inv, fun, args);

          // assume on_i ==> inv_i_replaced
          IToken tok_assume = new Token();
          Cmd new_assume = new AssumeCmd(tok_assume, on_imp_inv);
          simple_Cmds_third_bb.Add(new_assume);

          id++;
        }
        
        BigBlock third_bb = new BigBlock(tok_third_bb, label_name_third_bb, simple_Cmds_third_bb, null, null);

        res.Add(first_bb);
        res.Add(second_bb);
        res.Add(third_bb);
      }
      else { // we should not be here
        Console.WriteLine("Exception: loops_traversed.Count < 1");
        Console.WriteLine("    Method Transform_While (Labels): " + ec_while.Body.ParentBigBlock.LabelName);
      }

      return res;
    }
    // end Transform_While


    private static AssumeCmd Infer_Invariants_Stmt(IList<PredicateCmd> invariants, string loop_label, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed)
    {
      Expr assumption = new LiteralExpr(new Token(), true);
      BinaryOperator and_op = new BinaryOperator(new Token(), BinaryOperator.Opcode.And);
      BinaryOperator impl_op = new BinaryOperator(new Token(), BinaryOperator.Opcode.Imp);
      for (int i = 0; i < invariants.Count; i++)
      {
        int ident = i + 1;
        string actual_flag_name = loop_label + "_on_" + ident;
        Expr actual_flag = new IdentifierExpr(new Token(), actual_flag_name);
        string before_flag_name = loop_label + "_on_b_" + ident;
        Expr before_flag = new IdentifierExpr(new Token(), before_flag_name);
        string inductive_flag_name = loop_label + "_on_a_" + ident;
        Expr inductive_flag = new IdentifierExpr(new Token(), inductive_flag_name);
        Expr inv_replaced = Replace_Target_Names(invariants[i].Expr, targets_by_loop, targets_2_duplicates, loops_traversed);

        Expr inner_implication = new NAryExpr(new Token(), impl_op, new List<Expr> { inductive_flag, inv_replaced });
        Expr inner_conjunction = new NAryExpr(new Token(), and_op, new List<Expr> { before_flag, inner_implication });
        Expr implication = new NAryExpr(new Token(), impl_op, new List<Expr> { inner_conjunction, actual_flag });
        assumption = new NAryExpr(new Token(), and_op, new List<Expr> { assumption, implication });
      }
      return new AssumeCmd(new Token(), assumption);
    }

      // the method creates the statement of the form
      // if ( (on_b_1 && ... && on_b_n) && ((on_a_1 && ... && on_a_n) ==> (inv_replaced_1 && ... inv_replaced_n)) )
      //   then (assume on_1 && ... && on_n)
      // else if ...
      // and so on, with all possible invariants combinations
      private static IfCmd Infer_Invariants_Stmt_Complex(IList<PredicateCmd> invariants, string loop_label, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed)
    {
      IfCmd res;

      // create the list of all needed if statements
      List<IfCmd> if_list = new List<IfCmd>();
      int k = invariants.Count;
      for (int i = k; i > 0; i--)
      {
        List<IfCmd> k_choose_i_ifs = If_List_With_i_Invariants(invariants, loop_label, targets_by_loop, targets_2_duplicates, i, loops_traversed);
        if_list.AddRange(k_choose_i_ifs);
      }

      // concatenate the if statements from if_list into one big IfCmd
      int n = if_list.Count;
      for (int i = n-1; i > 0; i--)
      {
        if_list[i-1].elseIf = if_list[i];
      }

      res = if_list[0];
      return res;
    }
    // end Infer_Invariants_Stmt

    // the method creates a list of if statements of the form
    // if ( (on_b_k(1) && ... && on_b_k(i)) && ((on_a_k(1) && ... && on_a_k(i)) ==> (inv_replaced_k(1) && ... inv_replaced_k(i))) )
    //   then (assume on_k(1) && ... && on_k(i))
    // and so on, with all (k choose i) possible invariants combinations
    private static List<IfCmd> If_List_With_i_Invariants(IList<PredicateCmd> invariants, string loop_label, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, int i, List<string> loops_traversed)
    {
      List<IfCmd> res = new List<IfCmd>();
      int k = invariants.Count;

      // there are k choose i possible invariants combinations
      // we store lists of corresponding ids for each choice in a list
      List<List<int>> lists_of_inv_ids = Generate_Ids(k, i, 1);

      foreach (List<int> list in lists_of_inv_ids) {
        IfCmd new_if = Generate_If(list, invariants, loop_label, targets_by_loop, targets_2_duplicates, loops_traversed);
        res.Add(new_if);
      }
      return res;
    }
    // end If_List_With_i_Invariants

    // the method generates IfCmd for the method If_List_With_i_Invariants
    private static IfCmd Generate_If(List<int> list, IList<PredicateCmd> invariants, string loop_label, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed)
    {
      IfCmd res;

      IToken tok_if = new Token();
      Expr guard = Generate_Guard(list, invariants, loop_label, targets_by_loop, targets_2_duplicates, loops_traversed);
      StmtList then = Generate_Then(list, invariants, loop_label, targets_by_loop, targets_2_duplicates); 
      res = new IfCmd(tok_if, guard, then, null, null);

      return res;
    }

    // the method generates "then" argument for IfCmd constructor for the method Generate_If
    private static StmtList Generate_Then(List<int> indices_list, IList<PredicateCmd> invariants, string loop_label, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates)
    {
      StmtList res;

      IList<BigBlock> bbs = new List<BigBlock>();


      IToken tok_if_bb = new Token();

      string list2string = "_";
      foreach (int i in indices_list)
      {
        string i_s = i + "_";
        list2string = list2string + i_s;
      }
      string label = loop_label + list2string + indices_list.Count + "_invariants";

      // here we create Expr of the form on_1 && ... && on_k,
      // i.e. loop_label_on_id, where id is the invariant number from list parameter
      Expr[] idents = new Expr[indices_list.Count];
      int j = 0;
      foreach(int i in indices_list) {
        IToken tok_ident = new Token();
        string name_ident = loop_label + "_on_" + i;
        Expr new_ident = new IdentifierExpr(tok_ident, name_ident);
        idents[j] = new_ident;
        j++;
      }

      IToken tok_assume = new Token();
      Cmd new_assumeCmd;

      if (idents.Length == 1)
      {
        new_assumeCmd = new AssumeCmd(tok_assume, idents[0]);
      }
      else if (idents.Length > 1)
      {
        IList<Expr> args = new List<Expr>();
        args.Add(idents[0]);
        args.Add(idents[1]);
        IToken tok_fun = new Token();
        IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.And);
        IToken tok_nAryExpr = new Token();
        Expr expression = new NAryExpr(tok_nAryExpr, fun, args);
        for (int i = 2; i < idents.Length; i++) {
          IList<Expr> new_args = new List<Expr>();
          new_args.Add(expression);
          new_args.Add(idents[i]);
          IToken new_tok_fun = new Token();
          IAppliable new_fun = new BinaryOperator(new_tok_fun, BinaryOperator.Opcode.And);
          IToken new_tok_nAryExpr = new Token();
          Expr new_nAryExpr = new NAryExpr(new_tok_nAryExpr, new_fun, new_args);
          expression = new_nAryExpr;
        }
        new_assumeCmd = new AssumeCmd(tok_assume, expression);
      }
      else { // something went wrong
        Console.WriteLine("Exception in Method Generate_Then: idents.Length < 1");
        new_assumeCmd = null;
      }

      List<Cmd> simpleCmds = new List<Cmd>();
      simpleCmds.Add(new_assumeCmd);

      BigBlock if_bb = new BigBlock(tok_if_bb, label, simpleCmds, null, null);
      IToken tok_endCurly = new Token
      {
        val = "}"
      };

      bbs.Add(if_bb);
      res = new StmtList(bbs , tok_endCurly);
      return res;
    }
    // end Generate_Then

    // the method generates guard for IfCmd constructor for the method Generate_If
    private static Expr Generate_Guard(List<int> indices_list, IList<PredicateCmd> invariants, string loop_label, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed)
    {
      Expr res;

      // on_b_i(1) && ... && on_b_i(k)
      Expr[] idents_on_b = new Expr[indices_list.Count];
      int j = 0;
      foreach (int i in indices_list)
      {
        IToken tok_ident_on_b = new Token();
        string name_ident_on_b = loop_label + "_on_b_" + i;
        Expr new_ident_on_b = new IdentifierExpr(tok_ident_on_b, name_ident_on_b);
        idents_on_b[j] = new_ident_on_b;
        j++;
      }

      // on_a_i(1) && ... && on_a_i(k)
      Expr[] idents_on_a = new Expr[indices_list.Count];
      j = 0;
      foreach (int i in indices_list)
      {
        IToken tok_ident_on_a = new Token();
        string name_ident_on_a = loop_label + "_on_a_" + i;
        Expr new_ident_on_a = new IdentifierExpr(tok_ident_on_a, name_ident_on_a);
        idents_on_a[j] = new_ident_on_a;
        j++;
      }

      // inv_replaced_i(1) && ... && inv_replaced_i(k)
      Expr[] invs_replaced = new Expr[indices_list.Count];
      j = 0;
      foreach (int i in indices_list)
      {
        PredicateCmd inv = invariants[i - 1];
        Expr inv_replaced = Replace_Target_Names(inv.Expr, targets_by_loop, targets_2_duplicates, loops_traversed);
        invs_replaced[j] = inv_replaced;
        j++;
      }

      if (indices_list.Count == 1)
      {
        IList<Expr> args_1 = new List<Expr>();
        args_1.Add(idents_on_a[0]);
        args_1.Add(invs_replaced[0]);
        IToken tok_fun_1 = new Token();
        IAppliable fun_1 = new BinaryOperator(tok_fun_1, BinaryOperator.Opcode.Imp);
        IToken tok_expr_1 = new Token();
        NAryExpr expr_1 = new NAryExpr(tok_expr_1, fun_1, args_1);

        IList<Expr> args_2 = new List<Expr>();
        args_2.Add(idents_on_b[0]);
        args_2.Add(expr_1);
        IToken tok_fun_2 = new Token();
        IAppliable fun_2 = new BinaryOperator(tok_fun_2, BinaryOperator.Opcode.And);
        IToken tok_expr_2 = new Token();
        NAryExpr expr_2 = new NAryExpr(tok_expr_2, fun_2, args_2);

        res = expr_2;
        return res;
      }
      else if (indices_list.Count > 1)
      {
        IList<Expr> args_on_b = new List<Expr>();
        IList<Expr> args_on_a = new List<Expr>();
        IList<Expr> args_inv_id = new List<Expr>();
        args_on_b.Add(idents_on_b[0]);
        args_on_b.Add(idents_on_b[1]);
        args_on_a.Add(idents_on_a[0]);
        args_on_a.Add(idents_on_a[1]);
        args_inv_id.Add(invs_replaced[0]);
        args_inv_id.Add(invs_replaced[1]);

        IToken tok_fun_on_b = new Token();
        IToken tok_fun_on_a = new Token();
        IToken tok_fun_inv_id = new Token();
        IAppliable fun_on_b = new BinaryOperator(tok_fun_on_b, BinaryOperator.Opcode.And);
        IAppliable fun_on_a = new BinaryOperator(tok_fun_on_a, BinaryOperator.Opcode.And);
        IAppliable fun_inv_id = new BinaryOperator(tok_fun_inv_id, BinaryOperator.Opcode.And);

        IToken tok_nAryExpr_on_b = new Token();
        IToken tok_nAryExpr_on_a = new Token();
        IToken tok_nAryExpr_inv_id = new Token();
        Expr expr_on_b = new NAryExpr(tok_nAryExpr_on_b, fun_on_b, args_on_b);
        Expr expr_on_a = new NAryExpr(tok_nAryExpr_on_a, fun_on_a, args_on_a);
        Expr expr_inv_id = new NAryExpr(tok_nAryExpr_inv_id, fun_inv_id, args_inv_id);

        // on_b_i(1) && ... && on_b_i(k)
        // on_a_i(1) && ... && on_a_i(k)
        // inv_replaced_i(1) && ... && inv_replaced_i(k)
        for (int i = 2; i < indices_list.Count; i++)
        {
          IList<Expr> new_args_on_b = new List<Expr>();
          IList<Expr> new_args_on_a = new List<Expr>();
          IList<Expr> new_args_inv_id = new List<Expr>();
          new_args_on_b.Add(expr_on_b);
          new_args_on_b.Add(idents_on_b[i]);
          new_args_on_a.Add(expr_on_a);
          new_args_on_a.Add(idents_on_a[i]);
          new_args_inv_id.Add(expr_inv_id);
          new_args_inv_id.Add(invs_replaced[i]);

          IToken new_tok_fun_on_b = new Token();
          IToken new_tok_fun_on_a = new Token();
          IToken new_tok_fun_inv_id = new Token();
          IAppliable new_fun_on_b = new BinaryOperator(new_tok_fun_on_b, BinaryOperator.Opcode.And);
          IAppliable new_fun_on_a = new BinaryOperator(new_tok_fun_on_a, BinaryOperator.Opcode.And);
          IAppliable new_fun_inv_id = new BinaryOperator(new_tok_fun_inv_id, BinaryOperator.Opcode.And);

          IToken new_tok_nAryExpr_on_b = new Token();
          IToken new_tok_nAryExpr_on_a = new Token();
          IToken new_tok_nAryExpr_inv_id = new Token();
          Expr new_nAryExpr_on_b = new NAryExpr(new_tok_nAryExpr_on_b, new_fun_on_b, new_args_on_b);
          Expr new_nAryExpr_on_a = new NAryExpr(new_tok_nAryExpr_on_a, new_fun_on_a, new_args_on_a);
          Expr new_nAryExpr_inv_id = new NAryExpr(new_tok_nAryExpr_inv_id, new_fun_inv_id, new_args_inv_id);
          expr_on_b = new_nAryExpr_on_b;
          expr_on_a = new_nAryExpr_on_a;
          expr_inv_id = new_nAryExpr_inv_id;
        }

        // ( on_a_i(1) && ... && on_a_i(k) ) ==> ( inv_replaced_i(1) && ... && inv_replaced_i(k) )
        IList<Expr> args_on_a_imp_inv_id = new List<Expr>();
        args_on_a_imp_inv_id.Add(expr_on_a);
        args_on_a_imp_inv_id.Add(expr_inv_id);
        IToken tok_fun_on_a_imp_inv_id = new Token();
        IAppliable fun_on_a_imp_inv_id = new BinaryOperator(tok_fun_on_a_imp_inv_id, BinaryOperator.Opcode.Imp);
        IToken tok_expr_on_a_imp_inv_id = new Token();
        Expr expr_on_a_imp_inv_id = new NAryExpr(tok_expr_on_a_imp_inv_id, fun_on_a_imp_inv_id, args_on_a_imp_inv_id);

        // ( on_b_i(1) && ... && on_b_i(k) ) &&
        // ( on_a_i(1) && ... && on_a_i(k) ) ==> ( inv_replaced_i(1) && ... && inv_replaced_i(k) )
        IList<Expr> args = new List<Expr>();
        args.Add(expr_on_b);
        args.Add(expr_on_a_imp_inv_id);
        IToken tok_fun = new Token();
        IAppliable fun = new BinaryOperator(tok_fun, BinaryOperator.Opcode.And);
        IToken tok_expr = new Token();
        Expr expr_final = new NAryExpr(tok_expr, fun, args);
        res = expr_final;
        return res;
      }
      else
      { // something went wrong
        Console.WriteLine("Exception in Method Generate_Guard: list.Count < 1");
        res = null;
        return res;
      }
    }
    // end Generate_Guard

    // end Generate_If

    // method generates list of k choose i possible combinations of numbers from 1 to k inclusive
    private static List<List<int>> Generate_Ids(int k, int i, int start)
    {
      List<List<int>> res = new List<List<int>>();

      if (i == 0) // we should not be here
      {
        Console.WriteLine("Exception in Method Generate_Ids: i == 0");
        return res;
      }
      else if (i == 1) // end of recursion
      {
        for (int j = start; j < k - i + 2; j++)
        {
          List<int> new_list = new List<int>();
          new_list.Add(j);
          res.Add(new_list);
        }
        return res;
      }
      else
      {
        for (int j = start; j < k - i + 2; j++) {
          List<List<int>> lists = Generate_Ids(k, i - 1, j + 1);
          foreach (List<int> list in lists) {
            list.Insert(0, j);
          }
          res.AddRange(lists);
        }
        return res;
      }
    }
    // end Generate_Ids

    // method computes n choose k
    private static int N_Choose_K(int k, int i)
    {
      int res;

      // i!
      int i_fact = 1;
      for (int j = 2; j < i + 1; j++) {
        i_fact = i_fact * j;
      }

      // k * (k-1) * ... * (k-i+1)
      int k_fact = k;
      for (int j = 1; j < i; j++) {
        k_fact = k_fact * (k_fact - j);
      }

      res = k_fact / i_fact;
      return res;
    }
    // end N_Choose_K

    // the method transforms an "if" statement according to the encoding
    // corresponding to the in_loop flag
    private static StructuredCmd Transform_If(IfCmd ec_if, IList<PredicateCmd> invariants, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed, bool in_loop)
    {
      IfCmd res;

      IToken tok_if = new Token();
      Expr guard = null;
      StmtList then = null;
      IfCmd else_if = null;
      StmtList else_block = null;

      if (!in_loop)
      {
        guard = ec_if.Guard;
      }
      else {
        guard = Replace_Target_Names(ec_if.Guard, targets_by_loop, targets_2_duplicates, loops_traversed);
      }
      
      // chekc if branch
      if (ec_if.thn != null)
      {
        IList<BigBlock> then_transformed = new List<BigBlock>();

        if (!in_loop)
        {
          foreach (BigBlock bb in ec_if.thn.BigBlocks)
          {
            IList<BigBlock> bbs = Transform_BigBlock_not_in_loop(bb, invariants, targets_by_loop, targets_2_duplicates);
            foreach (BigBlock b in bbs)
            {
              then_transformed.Add(b);
            }
          }
        }
        else {
          foreach (BigBlock bb in ec_if.thn.BigBlocks)
          {
            IList<BigBlock> bbs = Transform_BigBlock_simulation_loop(bb, invariants, targets_by_loop, targets_2_duplicates, loops_traversed);
            foreach (BigBlock b in bbs)
            {
              then_transformed.Add(b);
            }
          }
        }
        IToken endCurly_then = new Token
        {
          val = "}"
        };
        then = new StmtList(then_transformed, endCurly_then);
      }

      // else if clause is implemented as nested if statements
      if (ec_if.elseIf != null)
      {
        else_if = (IfCmd)Transform_If(ec_if.elseIf, invariants, targets_by_loop, targets_2_duplicates, loops_traversed, in_loop);
      }

      // check else
      if (ec_if.elseBlock != null)
      {
        IList<BigBlock> else_transformed = new List<BigBlock>();

        if (!in_loop)
        {
          foreach (BigBlock bb in ec_if.elseBlock.BigBlocks)
          {
            IList<BigBlock> bbs = Transform_BigBlock_not_in_loop(bb, invariants, targets_by_loop, targets_2_duplicates);
            foreach (BigBlock b in bbs)
            {
              else_transformed.Add(b);
            }
          }
        }
        else
        {
          foreach (BigBlock bb in ec_if.elseBlock.BigBlocks)
          {
            IList<BigBlock> bbs = Transform_BigBlock_simulation_loop(bb, invariants, targets_by_loop, targets_2_duplicates, loops_traversed);
            foreach (BigBlock b in bbs)
            {
              else_transformed.Add(b);
            }
          }
        }
        IToken endCurly_else = new Token
        {
          val = "}"
        };
        else_block = new StmtList(else_transformed, endCurly_else);
      }

      res = new IfCmd(tok_if, guard, then, else_if, else_block);
      return res;
    }
    // end Transform_If

    // the method replaces target variable names 
    // by the corresponding duplicate varaibale names
    // in a given expression
    private static Expr Replace_Target_Names(Expr guard, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed)
    {
      Expr res = null;

      if (guard is LiteralExpr)
      {
        res = guard;
      }
      else if (guard is IdentifierExpr) {
        IdentifierExpr guard_ident = (IdentifierExpr)guard;
        // since the targets of outer loop also contain targets of all inner loops
        // it is enough to get only targets for the outer loop
        HashSet<string> outer_loop_targets;
        targets_by_loop.TryGetValue(loops_traversed[0], out outer_loop_targets);
        if (outer_loop_targets.Contains(guard_ident.Name))
        {
          IToken tok = new Token();
          string name;
          targets_2_duplicates.TryGetValue(guard_ident.Name, out name);
          IdentifierExpr new_ident = new IdentifierExpr(tok, name, guard_ident.Type);
          res = new_ident;
        }
        else
        {
          res = guard;
        }
      }
      else if (guard is NAryExpr) { // guard should be NAryExpr
        NAryExpr guard_expr = (NAryExpr)guard;
        IList<Expr> new_args = new List<Expr>();
        foreach (Expr e in guard_expr.Args) {
          Expr new_NAryExpr = Replace_Target_Names(e, targets_by_loop, targets_2_duplicates, loops_traversed);
          new_args.Add(new_NAryExpr);
        }
        IToken tok = new Token();
        NAryExpr new_expr = new NAryExpr(tok, guard_expr.Fun, new_args);
        res = new_expr;
      } else { // No idea what else an Expr could be 
        Console.WriteLine("Unknown type of guard: " + guard.Type);
        res = guard;
      }

      return res;
    }
    // end Replace_Target_Names

    // the method takes a BigBlock from an original Implementation 
    // the original BigBlock is transformed according to the corresponding encoding
    // for the sumulation of the loop
    // and returned as a new object (transformation is not in place)
    private static IList<BigBlock> Transform_BigBlock_simulation_loop(BigBlock b, IList<PredicateCmd> invariants, Dictionary<string, HashSet<string>> targets_by_loop, Dictionary<string, string> targets_2_duplicates, List<string> loops_traversed)
    {
      IList<BigBlock> res = new List<BigBlock>();

      // get targets
      HashSet<string> targ;
      targets_by_loop.TryGetValue(loops_traversed[0], out targ);

      // transform simpleCmds
      List<Cmd> sc = b.simpleCmds;
      List<Cmd> sc_transformed = new List<Cmd>();
      foreach (Cmd c in sc) {
        if (c is AssertCmd)
        { // "insert" skip
          continue;
        }
        else if (c is HavocCmd)
        {
          HavocCmd c_h = (HavocCmd)c;
          List<IdentifierExpr> h_vars = c_h.Vars;
          List<IdentifierExpr> h_vars_transformed = new List<IdentifierExpr>();
          foreach (IdentifierExpr v in h_vars)
          {
            if (targ.Contains(v.Name))
            {
              string dupl;
              targets_2_duplicates.TryGetValue(v.Name, out dupl);
              IToken tok_v_transformed = new Token();
              IdentifierExpr v_transformed = new IdentifierExpr(tok_v_transformed, dupl, v.Type);
              h_vars_transformed.Add(v_transformed);
            }
            else
            {
              h_vars_transformed.Add(v);
            }
          }
          IToken tok_havoc = new Token();
          HavocCmd c_h_transformed = new HavocCmd(tok_havoc, h_vars_transformed);

          sc_transformed.Add(c_h_transformed);
        }
        else if (c is AssumeCmd)
        {
          AssumeCmd c_a = (AssumeCmd)c;
          Expr e_transformed = Replace_Target_Names(c_a.Expr, targets_by_loop, targets_2_duplicates, loops_traversed);
          IToken tok_assume = new Token();
          AssumeCmd c_a_transformed = new AssumeCmd(tok_assume, e_transformed);
          sc_transformed.Add(c_a_transformed);
        }
        else if (c is AssignCmd) // also assignment of a result of a method call
        {
          AssignCmd c_a = (AssignCmd)c;

          // transform lhs
          IList<AssignLhs> lhss_transformed = new List<AssignLhs>();

          for (int i = 0; i < c_a.Lhss.ToList().Count; i++)
          {
            string name_lhs_transformed;
            AssignLhs lhs = c_a.Lhss.ToList()[i];
            string name_lhs = lhs.DeepAssignedIdentifier.Name;
            if (targ.Contains(name_lhs))
            {
              targets_2_duplicates.TryGetValue(name_lhs, out name_lhs_transformed);
            }
            else
            {
              name_lhs_transformed = name_lhs;
            }

            IToken tok_lhs_expr = new Token();
            IdentifierExpr lhs_expr = new IdentifierExpr(tok_lhs_expr, name_lhs_transformed);
            IToken tok_simple_assign = new Token();
            AssignLhs lhs_transformed;
            if ((lhs as MapAssignLhs) != null)
            {
              lhs_transformed = new SimpleAssignLhs(tok_simple_assign, lhs_expr);
              List<Expr> indices = new List<Expr>();
              foreach (Expr index in (lhs as MapAssignLhs).Indexes)
              {
                indices.Add(Replace_Target_Names(index, targets_by_loop, targets_2_duplicates, loops_traversed));
              }
              lhs_transformed = new MapAssignLhs(tok_simple_assign, lhs_transformed, indices);
            }
            else
            {
              lhs_transformed = new SimpleAssignLhs(tok_simple_assign, lhs_expr);
            }


            lhss_transformed.Add(lhs_transformed);
          }



          // transform rhs
          IList<Expr> rhss_transformed = new List<Expr>();

          for (int i = 0; i < c_a.Rhss.ToList().Count; i++)
          {
            Expr rhs_expr = Replace_Target_Names(c_a.Rhss.ToList()[i], targets_by_loop, targets_2_duplicates, loops_traversed);

            rhss_transformed.Add(rhs_expr);
          }
          IToken tok_assign = new Token();
          AssignCmd c_a_transformed = new AssignCmd(tok_assign, lhss_transformed, rhss_transformed);

          sc_transformed.Add(c_a_transformed);

        }
        else if (c is CallCmd) 
        {
          CallCmd call = c as CallCmd;
          List<Expr> transformedIns = new List<Expr>();
          List<IdentifierExpr> transformedOuts = new List<IdentifierExpr>();
          foreach (Expr inexp in call.Ins)
          {
            transformedIns.Add(Replace_Target_Names(inexp, targets_by_loop, targets_2_duplicates, loops_traversed));
          }
          foreach (Expr outexp in call.Outs)
          {
            transformedOuts.Add(Replace_Target_Names(outexp, targets_by_loop, targets_2_duplicates, loops_traversed) as IdentifierExpr);
          }
          sc_transformed.Add(new CallCmd(new Token(), call.callee, transformedIns, transformedOuts));
        }
        else // some unknown command
        {
          Console.WriteLine("Method Transform_BigBlock_simulation_loop: unknown simpleCmd:");
          Console.WriteLine("    " + c);
          sc_transformed.Add(c);
        }
      }
      // transformed simpleCmds are now in sc_transformed

      // no implementation for BreakCmd for now
      
      if (b.ec is WhileCmd)
      {
        WhileCmd ec_while = (WhileCmd)b.ec;
        loops_traversed.Add(b.LabelName);
        res = Transform_While(ec_while, sc_transformed, invariants, targets_by_loop, targets_2_duplicates, loops_traversed);
      }
      else if (b.ec is IfCmd)
      {
        IToken t_transformed = new Token();
        string label_transformed = b.LabelName + "_transformed";
        
        // I do not know, what it is
        TransferCmd tc_transformed = b.tc;

        IfCmd ec_if = (IfCmd)b.ec;
        StructuredCmd ec_transformed;
        ec_transformed = Transform_If(ec_if, invariants, targets_by_loop, targets_2_duplicates, loops_traversed, true);

        BigBlock b_transformed = new BigBlock(t_transformed, label_transformed, sc_transformed, ec_transformed, tc_transformed);
        res.Add(b_transformed);
      }
      else
      {
        IToken t_transformed = new Token();
        string label_transformed = b.LabelName + "_transformed";
        
        // I do not know, what it is
        TransferCmd tc_transformed = b.tc;

        StructuredCmd ec_transformed;
        ec_transformed = b.ec;

        BigBlock b_transformed = new BigBlock(t_transformed, label_transformed, sc_transformed, ec_transformed, tc_transformed);
        res.Add(b_transformed);
      }

      return res;
    }
    // end transform_BigBlock_simulation_loop

    // the method takes a BigBlock from an original Implementation 
    // the original BigBlock is transformed according to the and corresponding encoding
    // for original loop
    // and returned as a new object (transformation is not in place)
    private static IList<BigBlock> Transform_BigBlock_original_loop(BigBlock b, IList<PredicateCmd> invariants, Dictionary<string, HashSet<string>> targets_by_loop, List<string> loops_traversed)
    {
      IList<BigBlock> res = new List<BigBlock>();

      // no implementation for BreakCmd for now

      if (b.ec is WhileCmd) // the only statement wich needs to be transformed
      {
        WhileCmd ec_while = (WhileCmd)b.ec;
        loops_traversed.Add(b.LabelName);
        res = Transform_While_original_loop(ec_while, b.simpleCmds, invariants, targets_by_loop, loops_traversed);
      }
      else if (b.ec is IfCmd)
      {
        IfCmd ec_if = (IfCmd)b.ec;

        IToken t_transformed = new Token();
        string label_transformed = b.LabelName;
        List<Cmd> simpleCmds_transformed = b.simpleCmds;

        // transform if
        StructuredCmd if_transformed = Transform_If_original_loop(ec_if, invariants, targets_by_loop, loops_traversed);

        // I do not know, what it is
        TransferCmd tc_transformed = b.tc;

        BigBlock b_transformed = new BigBlock(t_transformed, label_transformed, simpleCmds_transformed, if_transformed, tc_transformed);
        res.Add(b_transformed);
      }
      else
      { // also b.ec == null case is covered
        IToken t_transformed = new Token();
        string label_transformed = b.LabelName;
        List<Cmd> simpleCmds_transformed = b.simpleCmds;

        // I do not know, what it is
        TransferCmd tc_transformed = b.tc;

        StructuredCmd ec_transformed;
        ec_transformed = b.ec;

        BigBlock b_transformed = new BigBlock(t_transformed, label_transformed, simpleCmds_transformed, ec_transformed, tc_transformed);
        res.Add(b_transformed);
      }

      return res;
    }
    // end Transform_BigBlock_original_loop

    // the method transforms while statement according to the actual loop encoding
    // only while statements (in input's BigBlocks) are transformed
    private static IList<BigBlock> Transform_While_original_loop(WhileCmd ec_while, List<Cmd> simpleCmds, IList<PredicateCmd> invariants, Dictionary<string, HashSet<string>> targets_by_loop, List<string> loops_traversed)
    {
      IList<BigBlock> res = new List<BigBlock>();

      int last_loop_index = loops_traversed.Count - 1;
      
      // star_id := havoc
      IToken tok_star = new Token();
      string name_star = loops_traversed[last_loop_index] + "_star";
      IdentifierExpr star = new IdentifierExpr(tok_star, name_star);
      List<IdentifierExpr> vars_star = new List<IdentifierExpr>();
      vars_star.Add(star);
      IToken tok_havoc_star = new Token();
      Cmd havoc_star = new HavocCmd(tok_havoc_star, vars_star);

      simpleCmds.Add(havoc_star);

      // havoc targets
      HashSet<string> targs;
      targets_by_loop.TryGetValue(loops_traversed[last_loop_index], out targs);
      foreach (string t in targs) {
        IToken tok_t = new Token();
        IdentifierExpr t_expr = new IdentifierExpr(tok_t, t);
        List<IdentifierExpr> vars_t = new List<IdentifierExpr>();
        vars_t.Add(t_expr);
        IToken tok_havoc_t = new Token();
        Cmd havoc_t = new HavocCmd(tok_havoc_t, vars_t);

        simpleCmds.Add(havoc_t);
      }

      // assume on ==> inv
      int id = 1;
      foreach (PredicateCmd inv in invariants) {
        // on
        IToken tok_on = new Token();
        string name_on = loops_traversed[last_loop_index] + "_on_" + id;
        Expr on = new IdentifierExpr(tok_on, name_on);

        // inv
        Expr inv_expr = inv.Expr;

        // on ==> inv
        IList<Expr> args_imp = new List<Expr>();
        args_imp.Add(on);
        args_imp.Add(inv_expr);
        IToken tok_fun_imp_expr = new Token();
        IAppliable fun_imp_expr = new BinaryOperator(tok_fun_imp_expr, BinaryOperator.Opcode.Imp);
        IToken tok_imp_expr = new Token();
        Expr imp_expr = new NAryExpr(tok_imp_expr, fun_imp_expr, args_imp);
        Token tok_a_c = new Token(); 
        Cmd a_c = new AssumeCmd(tok_a_c, imp_expr);

        simpleCmds.Add(a_c);

        id++;
      }

      // if (star) then ...

      // then 
      IToken tok_assume_c = new Token();
      Cmd assume_c = new AssumeCmd(tok_assume_c, ec_while.Guard);

      IList<BigBlock> then_bbs = new List<BigBlock>();
      foreach (BigBlock bb in ec_while.Body.BigBlocks)
      {
        IList<BigBlock> bb_transformed = Transform_BigBlock_original_loop(bb, invariants, targets_by_loop, loops_traversed);
        foreach (BigBlock b_tr in bb_transformed)
        {
          then_bbs.Add(b_tr);
        }
      }
      then_bbs.ToList()[0].simpleCmds.Insert(0, assume_c);

      // assume false BigBlock
      // if necessary
      IToken tok_lit = new Token();
      Expr false_lit = new LiteralExpr(tok_lit, false);
      IToken tok_assume_false = new Token();
      Cmd assume_false_cmd = new AssumeCmd(tok_assume_false, false_lit);

      int last_index = then_bbs.Count - 1;
      if (then_bbs[last_index].ec != null)
      {
        List<Cmd> false_lit_list = new List<Cmd>();
        false_lit_list.Add(assume_false_cmd);

        IToken tok_assume_false_bb = new Token();
        string label_assume_false_bb = loops_traversed[0] + "_assume_false_bb";
        BigBlock assume_false_bb = new BigBlock(tok_assume_false_bb, label_assume_false_bb, false_lit_list, null, null);

        then_bbs.Add(assume_false_bb);
      }
      else
      {
        then_bbs[last_index].simpleCmds.Add(assume_false_cmd);
      }

      IToken endCurly_then = new Token
      {
        val = "}"
      };
      StmtList then = new StmtList(then_bbs, endCurly_then);

      // else if
      IfCmd else_if = null;

      // else
      IList<Expr> args_not_loop_condition = new List<Expr>();
      args_not_loop_condition.Add(ec_while.Guard);
      IToken tok_fun_not_loop_condition = new Token();
      IAppliable fun_not_loop_condition = new UnaryOperator(tok_fun_not_loop_condition, UnaryOperator.Opcode.Not);
      IToken tok_not_loop_condition = new Token();
      Expr not_loop_condition = new NAryExpr(tok_not_loop_condition, fun_not_loop_condition, args_not_loop_condition);

      IToken tok_assume_not_loop_condition = new Token();
      Cmd assume_not_loop_condition = new AssumeCmd(tok_assume_not_loop_condition, not_loop_condition);
      List<Cmd> cmd_negate_loop_condition = new List<Cmd>();
      cmd_negate_loop_condition.Add(assume_not_loop_condition);

      IToken tok_negate_loop_condition = new Token();
      string name_negate_loop_condition = loops_traversed[last_loop_index] + "_negate_loop_condition_bb";
      BigBlock negate_loop_condition = new BigBlock(tok_negate_loop_condition, name_negate_loop_condition, cmd_negate_loop_condition, null, null);
      IList<BigBlock> else_bbs_list = new List<BigBlock>();
      else_bbs_list.Add(negate_loop_condition);
      IToken endCurly_else = new Token
      {
        val = "}"
      };
      StmtList else_stmt = new StmtList(else_bbs_list, endCurly_else);


      IToken tok_guard = new Token();
      string name_guard = loops_traversed[last_loop_index] + "_star";
      Expr guard = new IdentifierExpr(tok_guard, name_guard);
      IToken tok_if = new Token();
      StructuredCmd if_cmd = new IfCmd(tok_if, guard, then, else_if, else_stmt);

      IToken tok_bb = new Token();
      BigBlock new_bb = new BigBlock(tok_bb, loops_traversed[last_loop_index], simpleCmds, if_cmd, null);

      res.Add(new_bb);
      return res;
    }
    // end Transform_While_original_loop

    // method transforms if statement corresponding to the actual loop encoding
    // only while statements inside if are transformed
    private static IfCmd Transform_If_original_loop(IfCmd ec_if, IList<PredicateCmd> invariants, Dictionary<string, HashSet<string>> targets_by_loop, List<string> loops_traversed)
    {
      IfCmd res;

      // then
      IList<BigBlock> then_bbs = new List<BigBlock>();
      foreach (BigBlock bb in ec_if.thn.BigBlocks)
      {
        IList<BigBlock> bb_transformed = Transform_BigBlock_original_loop(bb, invariants, targets_by_loop, loops_traversed);
        foreach (BigBlock b_tr in bb_transformed)
        {
          then_bbs.Add(b_tr);
        }
      }
      IToken endCurly_then = new Token
      {
        val = "}"
      };
      StmtList then = new StmtList(then_bbs, endCurly_then);

      // else if
      IfCmd else_if = null;
      if (ec_if.elseIf != null) {
        else_if = Transform_If_original_loop(ec_if.elseIf, invariants, targets_by_loop, loops_traversed);
      }

      // else
      StmtList else_stmt = null;
      if (ec_if.elseBlock != null) {
        IList<BigBlock> else_bbs = new List<BigBlock>();
        foreach (BigBlock bb in ec_if.elseBlock.BigBlocks)
        {
          IList<BigBlock> bb_transformed = Transform_BigBlock_original_loop(bb, invariants, targets_by_loop, loops_traversed);
          foreach (BigBlock b_tr in bb_transformed)
          {
            else_bbs.Add(b_tr);
          }
        }
        IToken endCurly_else = new Token
        {
          val = "}"
        };
        else_stmt = new StmtList(else_bbs, endCurly_else);
      }

      IToken tok_if_cmd = new Token();
      IfCmd ec_transformed = new IfCmd(tok_if_cmd, ec_if.Guard, then, else_if, else_stmt);

      res = ec_transformed;
      return res;
    }
    // end Transform_If_original_loop

    // the method returns duplicates of all target variables
    // parameters: original list of local variables, names of target variables 
    private static HashSet<Variable> Get_Target_Variables_Duplicates(List<Variable> locVars, List<Variable> outParams, HashSet<string> target_names, out Dictionary<string, string> targets_2_duplicates)
    {
      HashSet<Variable> res = new HashSet<Variable>();
      targets_2_duplicates = new Dictionary<string, string>();

      foreach (string s in target_names) {
        bool match_found = false;

        foreach (Variable v in locVars) {
          if (s == v.Name) {
            // fill the mapping in
            targets_2_duplicates.Add(s, s + "_duplicate");

            // create duplicate variable
            IToken tok_for_basicType = new Token();
            BasicType b_type;
            if (v.TypedIdent.Type.IsInt)
            {
              b_type = new BasicType(tok_for_basicType, SimpleType.Int);
            }
            else if (v.TypedIdent.Type.IsReal)
            {
              b_type = new BasicType(tok_for_basicType, SimpleType.Real);
            }
            else if (v.TypedIdent.Type.IsBool)
            {
              b_type = new BasicType(tok_for_basicType, SimpleType.Bool);
            }
            else {
              b_type = new BasicType(tok_for_basicType, SimpleType.RMode);
            }
      
            IToken tok_for_typeIdent = new Token();
            string name_duplicate = v.Name + "_duplicate";
            TypedIdent t_Ident = new TypedIdent(tok_for_typeIdent, name_duplicate, v.TypedIdent.Type);

            IToken tok_for_var = new Token();
            LocalVariable var_duplicate = new LocalVariable(tok_for_var, t_Ident);

            res.Add(var_duplicate);
            match_found = true;
            break;
          }          
        }

        if (!match_found)
        {
          foreach (Variable v in outParams)
          {
            if (s == v.Name)
            {
              // fill the mapping in
              targets_2_duplicates.Add(s, s + "_duplicate");

              // create duplicate variable
              IToken tok_for_basicType = new Token();
              BasicType b_type;
              if (v.TypedIdent.Type.IsInt)
              {
                b_type = new BasicType(tok_for_basicType, SimpleType.Int);
              }
              else if (v.TypedIdent.Type.IsReal)
              {
                b_type = new BasicType(tok_for_basicType, SimpleType.Real);
              }
              else if (v.TypedIdent.Type.IsBool)
              {
                b_type = new BasicType(tok_for_basicType, SimpleType.Bool);
              }
              else
              {
                b_type = new BasicType(tok_for_basicType, SimpleType.RMode);
              }

              IToken tok_for_typeIdent = new Token();
              string name_duplicate = v.Name + "_duplicate";
              TypedIdent t_Ident = new TypedIdent(tok_for_typeIdent, name_duplicate, b_type);

              IToken tok_for_var = new Token();
              LocalVariable var_duplicate = new LocalVariable(tok_for_var, t_Ident);

              res.Add(var_duplicate);
              break;
            }
          }
        }

        match_found = false;
      }
      
      return res;
    }
    // end Get_Target_Variables_Duplicates

    // the method extracts all target variables relative to the corresponding loop from a given BigBlock
    // the variables are added to the dictionary according to the id of the loop they were found in
    // if a variable is inside a nested loop, it appears in a dictionary once for each loop id 
    private static Dictionary<string, HashSet<string>> Collect_Target_Names_by_Loop(BigBlock bb, HashSet<string> loop_labels, bool in_loop)
    {
      Dictionary<string, HashSet<string>> res = new Dictionary<string, HashSet<string>>();

      // first we check, what is inside StructuredCmd field
      if (bb.ec != null)
      {
        if (bb.ec is IfCmd)
        {
          IfCmd ec_if = (IfCmd)bb.ec;
          Dictionary<string, HashSet<string>> targets_by_loop_from_if = Collect_Targets_by_Loop_From_If(ec_if, loop_labels, in_loop);
          res = MergeDictionaries(res, targets_by_loop_from_if);
        }
        else if (bb.ec is WhileCmd)
        {
          WhileCmd ec_while = (WhileCmd)bb.ec;
          HashSet<string> new_loop_labels = new HashSet<string>();
          new_loop_labels.UnionWith(loop_labels);
          new_loop_labels.Add(bb.LabelName);
          Dictionary<string, HashSet<string>> targets_by_loop_from_while = Collect_Targets_by_Loop_From_While(ec_while, new_loop_labels);
          res = MergeDictionaries(res, targets_by_loop_from_while);
        }
      }

      // if we are already inside a loop,
      // we have to collect the target variables
      if (in_loop)
      {
        if (bb.simpleCmds.Count > 0)
        {
          foreach (Cmd c in bb.simpleCmds)
          {
            // we care only about assignments and need to the name of variable from the left side 
            if (c is AssignCmd)
            {
              AssignCmd ac = (AssignCmd)c;
              // apparently there can be several left hand sides, so we use Lhss[0]
              // TODO: exception, if more then one left hand side
              for (int i = 0; i < ac.Lhss.Count; i++)
              {
                string var_name = ac.Lhss[i].DeepAssignedIdentifier.Name;

                foreach (string s in loop_labels)
                {
                  if (!res.ContainsKey(s))
                  {
                    HashSet<string> vals = new HashSet<string>();
                    vals.Add(var_name);
                    res.Add(s, vals);
                  }
                  res[s].Add(var_name);
                }
              }

            }
          }         
        }
      }

      return res;
    }
    // end Collect_Target_Names_by_Loop


    private static Dictionary<string, HashSet<string>> Collect_Targets_by_Loop_From_While(WhileCmd ec_while, HashSet<string> loop_labels)
    {
      Dictionary<string, HashSet<string>> res = new Dictionary<string, HashSet<string>>();

      foreach (BigBlock bb in ec_while.Body.BigBlocks)
      {
        Dictionary<string, HashSet<string>> targets_by_loop = Collect_Target_Names_by_Loop(bb, loop_labels, true); 
        res = MergeDictionaries(res, targets_by_loop);
      }

      return res;
    }
    // end Collect_Targets_by_Loop_From_While

    private static Dictionary<string, HashSet<string>> Collect_Targets_by_Loop_From_If(IfCmd ec_if, HashSet<string> loop_labels, bool in_loop)
    {
      Dictionary<string, HashSet<string>> res = new Dictionary<string, HashSet<string>>();

      // chekc if branch
      if (ec_if.thn != null)
      {
        foreach (BigBlock bb in ec_if.thn.BigBlocks)
        {
          Dictionary<string, HashSet<string>> targets_by_loop = Collect_Target_Names_by_Loop(bb, loop_labels, in_loop);
          res = MergeDictionaries(res, targets_by_loop);
        }
      }

      // else if clause is implemented as nested if statements
      if (ec_if.elseIf != null)
      {
        Dictionary<string, HashSet<string>> targets_by_loop = Collect_Targets_by_Loop_From_If(ec_if.elseIf, loop_labels, in_loop);
        res = MergeDictionaries(res, targets_by_loop);
      }

      // check else
      if (ec_if.elseBlock != null)
      {
        foreach (BigBlock bb in ec_if.elseBlock.BigBlocks)
        {
          Dictionary<string, HashSet<string>> targets_by_loop = Collect_Target_Names_by_Loop(bb, loop_labels, in_loop);
          res = MergeDictionaries(res, targets_by_loop);
        }
      }

      return res;
    }
    // end Collect_Targets_by_Loop_From_If

    public static HashSet<string> GetTargetNames(BigBlock bb, bool in_loop)
    {
      HashSet<string> res = new HashSet<string>();

      // first we check, what is inside StructuredCmd field
      if (bb.ec != null)
      {
        if (bb.ec is IfCmd)
        {
          IfCmd ec_if = (IfCmd)bb.ec;
          res.UnionWith( GetTargetsFromIf(ec_if, in_loop) );
        }
        else if (bb.ec is WhileCmd)
        {
          WhileCmd ec_while = (WhileCmd)bb.ec;
          res.UnionWith( GetTargetsFromWhile(ec_while) );
        }
      }
      
      // if we are already inside a loop,
      // we have to collect the target variables
      if (in_loop)
      {
        if (bb.simpleCmds.Count > 0)
        {
          foreach (Cmd c in bb.simpleCmds)
          {
            // we care only about assignments and need to the name of variable from the left side 
            if (c is AssignCmd)
            {
              AssignCmd ac = (AssignCmd)c;
              // apparently there can be several left hand sides, so we use Lhss[0]
              // TODO: exception, if more then one left hand side
              for (int i = 0; i < ac.Lhss.Count; i++)
              {
                string var_name = ac.Lhss[i].DeepAssignedIdentifier.Name;
                res.Add(var_name);
              }

            }
          }
        }
      }

      return res;
    }
    // end GetTargetsNames

    private static HashSet<string> GetTargetsFromWhile(WhileCmd ec_while)
    {
      HashSet<string> res = new HashSet<string>();

      foreach (BigBlock bb in ec_while.Body.BigBlocks)
      {
        res.UnionWith( GetTargetNames(bb, true) );
      } 

      return res;
    }
    // end GetTargetsFromWhile

    public static HashSet<string> GetTargetsFromIf(IfCmd ec_if, bool in_loop) 
    {
      HashSet<string> res = new HashSet<string>();

      // chekc if branch
      if (ec_if.thn != null)
      {
        foreach (BigBlock bb in ec_if.thn.BigBlocks)
        {
          res.UnionWith( GetTargetNames(bb, in_loop) );
        }
      }

      // else if clause is implemented as nested if statements
      if (ec_if.elseIf != null)
      { 
        res.UnionWith( GetTargetsFromIf(ec_if.elseIf, in_loop) );       
      }

      // check else
      if (ec_if.elseBlock != null)
      {
        foreach (BigBlock bb in ec_if.elseBlock.BigBlocks)
        {
          res.UnionWith( GetTargetNames(bb, in_loop) );
        }
      }

      return res;
    }
    // end GetTargetsFromIf

    // the method merges two Dictionaries based on their keys
    // if a key is present in both dictionaries, union over the corresponding values is computed
    // returns a new Dictionary
    private static Dictionary<string, HashSet<string>> MergeDictionaries(Dictionary<string, HashSet<string>> d1, Dictionary<string, HashSet<string>> d2)
    {
      Dictionary<string, HashSet<string>> res = new Dictionary<string, HashSet<string>>();
      foreach (KeyValuePair<string, HashSet<string>> key_value in d1)
      {
        res.Add(key_value.Key, key_value.Value);
      }

      foreach (KeyValuePair<string, HashSet<string>> key_value in d2)
      {
        if (!res.ContainsKey(key_value.Key))
        {
          res.Add(key_value.Key, key_value.Value);
        }
        else
        {
          HashSet<string> res_targets = res[key_value.Key];
          HashSet<string> from_if_targets = d2[key_value.Key];
          res_targets.UnionWith(from_if_targets);
          res[key_value.Key] = res_targets;
        }
      }

      return res;
    }
    // end MergeDictionaries

    // the method prints the program text to the console or file
    // it is here for debuging / development purposes only 
    public static void PrintBplFile(string filename, Program program, bool allowPrintDesugaring, bool setTokens = true, bool pretty = false)
    {
      Contract.Requires(program != null);
      Contract.Requires(filename != null);
      bool oldPrintDesugaring = CommandLineOptions.Clo.PrintDesugarings;
      if (!allowPrintDesugaring)
      {
        CommandLineOptions.Clo.PrintDesugarings = false;
      }
      using (TokenTextWriter writer = filename == "-" ?
                                      new TokenTextWriter("<console>", Console.Out, setTokens, pretty) :
                                      new TokenTextWriter(filename, setTokens, pretty))
      {
        if (CommandLineOptions.Clo.ShowEnv != CommandLineOptions.ShowEnvironment.Never)
        {
          writer.WriteLine("// " + CommandLineOptions.Clo.Version);
          writer.WriteLine("// " + CommandLineOptions.Clo.Environment);
        }
        writer.WriteLine();
        program.Emit(writer);
      }
      CommandLineOptions.Clo.PrintDesugarings = oldPrintDesugaring;
    }
    // end PrintBplFile

  }
  // end class Translator

}
// end namespace Core
