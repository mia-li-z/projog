package org.projog.build;

import static org.projog.build.BuildUtilsConstants.DOCS_OUTPUT_DIR;
import static org.projog.build.BuildUtilsConstants.HTML_FILE_EXTENSION;
import static org.projog.build.BuildUtilsConstants.TEXT_FILE_EXTENSION;
import static org.projog.build.BuildUtilsConstants.readFile;

import java.io.File;
import java.util.List;

/**
 * Represents a web page containing example Prolog queries and responses.
 */
class CodeExampleWebPage {
   static CodeExampleWebPage create(File prologSourceFile) {
      File htmlFile = getHtmlFile(prologSourceFile);
      File textFile = getTextFile(prologSourceFile);
      List<String> textFileContents = readFile(textFile);
      String title = textFileContents.remove(0);
      return new CodeExampleWebPage(title, textFileContents, prologSourceFile, htmlFile);
   }

   private static File getHtmlFile(File scriptFile) {
      String nameMinusExtension = getFileNameMinusExtension(scriptFile);
      String htmlFileName = nameMinusExtension + HTML_FILE_EXTENSION;
      return new File(DOCS_OUTPUT_DIR, htmlFileName);
   }

   private static File getTextFile(File scriptFile) {
      String nameMinusExtension = getFileNameMinusExtension(scriptFile);
      String textFileName = nameMinusExtension + TEXT_FILE_EXTENSION;
      return new File(scriptFile.getParentFile(), textFileName);
   }

   private static String getFileNameMinusExtension(File file) {
      String fileName = file.getName();
      int dotPos = fileName.indexOf('.');
      return fileName.substring(0, dotPos);
   }

   private final String title;
   private final List<String> description;
   private final File prologSourceFile;
   private final File htmlFile;

   private CodeExampleWebPage(String title, List<String> description, File prologSourceFile, File htmlFile) {
      this.title = title;
      this.description = description;
      this.prologSourceFile = prologSourceFile;
      this.htmlFile = htmlFile;
   }

   String getTitle() {
      return title;
   }

   List<String> getDescription() {
      return description;
   }

   File getPrologSourceFile() {
      return prologSourceFile;
   }

   File getHtmlFile() {
      return htmlFile;
   }

   String getHtmlFileName() {
      return htmlFile.getName();
   }
}